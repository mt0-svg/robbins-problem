import Robbins.Statement

/-!
# Integrating out one value

`law (n + 1)` is `law n` times the uniform law of the last value (`integral_law_succ_snoc`), or the
uniform law of the first value times `law n` (`integral_law_succ_cons`).
-/

namespace Robbins

open MeasureTheory

theorem ae_mem_Icc (n : ℕ) : ∀ᵐ x ∂law n, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  have h_tendsto : Filter.Tendsto (fun x : Fin n → ℝ => x j) (MeasureTheory.ae (law n))
      (MeasureTheory.ae (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    simpa [law] using MeasureTheory.Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) (i := j)
  have h_mem : ∀ᵐ a ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), a ∈ Set.Icc (0 : ℝ) 1 :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  simpa using h_tendsto.eventually h_mem

theorem integral_law_succ_snoc {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f (law (n + 1))) :
    ∫ x, f x ∂law (n + 1) = ∫ y, (∫ a in Set.Icc (0 : ℝ) 1, f (Fin.snoc (α := fun _ => ℝ) y a)) ∂law n := by
  set μ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have h_mp : MeasurePreserving (e : (Fin (n + 1) → ℝ) → ℝ × (Fin n → ℝ))
      (law (n + 1)) (μ.prod (law n)) := by
    dsimp [law, μ]
    exact measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)
  have h_int_comp : Integrable (f ∘ e.symm) (μ.prod (law n)) :=
    h_mp.symm.integrable_comp_of_integrable hf
  have h_symm_eq (a : ℝ) (y : Fin n → ℝ) : e.symm (a, y) = Fin.snoc (α := fun _ => ℝ) y a := by
    dsimp [e]
    have h := MeasurableEquiv.piFinSuccAbove_symm_apply (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
    -- h : ⇑(MeasurableEquiv.piFinSuccAbove ...).symm = ⇑(Fin.insertNthEquiv ...)
    calc
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm (a, y) =
          (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) (a, y) := by
        simpa using congrFun h (a, y)
      _ = Fin.insertNth (Fin.last n) a y := rfl
      _ = Fin.snoc (α := fun _ => ℝ) y a := by simpa using Fin.insertNth_last' a y
  calc
    ∫ x, f x ∂law (n + 1) = ∫ p, f (e.symm p) ∂(μ.prod (law n)) := by
      -- h_mp.integral_comp' (f ∘ e.symm) : ∫ x, (f ∘ e.symm) (e x) ∂law (n+1) = ∫ p, (f ∘ e.symm) p ∂(μ.prod (law n))
      -- (f ∘ e.symm) (e x) = f x and (f ∘ e.symm) p = f (e.symm p)
      calc
        ∫ x, f x ∂law (n + 1) = ∫ x, f (e.symm (e x)) ∂law (n + 1) := by simp
        _ = ∫ x, (f ∘ e.symm) (e x) ∂law (n + 1) := rfl
        _ = ∫ p, (f ∘ e.symm) p ∂(μ.prod (law n)) := h_mp.integral_comp' (f ∘ e.symm)
        _ = ∫ p, f (e.symm p) ∂(μ.prod (law n)) := rfl
    _ = ∫ y, ∫ a, f (e.symm (a, y)) ∂μ ∂law n := by
      simpa using integral_prod_symm (f ∘ e.symm) h_int_comp
    _ = ∫ y, ∫ a, f (Fin.snoc (α := fun _ => ℝ) y a) ∂μ ∂law n := by
      simp [h_symm_eq]
    _ = ∫ y, (∫ a in Set.Icc (0 : ℝ) 1, f (Fin.snoc (α := fun _ => ℝ) y a)) ∂law n := by
      simp [μ]

theorem integral_law_succ_cons {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f (law (n + 1))) :
    ∫ x, f x ∂law (n + 1) = ∫ a in Set.Icc (0 : ℝ) 1, (∫ y, f (Fin.cons (α := fun _ => ℝ) a y) ∂law n) := by
  set μ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  set e := MeasurableEquiv.piFinSuccAbove (fun (_ : Fin (n + 1)) => ℝ) 0 with he
  have h_mp : MeasurePreserving e (law (n + 1)) (μ.prod (law n)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) 0
  have h_mp_symm : MeasurePreserving e.symm (μ.prod (law n)) (law (n + 1)) :=
    h_mp.symm
  have h_int_comp : (∫ p : ℝ × (Fin n → ℝ), f (e.symm p) ∂(μ.prod (law n))) =
                   (∫ x : Fin (n + 1) → ℝ, f x ∂law (n + 1)) :=
    h_mp_symm.integral_comp' f
  have h_symm_eq : ∀ (p : ℝ × (Fin n → ℝ)), e.symm p = Fin.cons (α := fun _ => ℝ) p.1 p.2 := by
    intro p
    calc
      e.symm p = (Fin.insertNthEquiv (fun (_ : Fin (n + 1)) => ℝ) 0) p := by
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      _ = Fin.cons (α := fun _ => ℝ) p.1 p.2 := by
        ext i
        simp [Fin.insertNthEquiv, Fin.cons]
  have h_int_comp' : (∫ p : ℝ × (Fin n → ℝ), f (Fin.cons (α := fun _ => ℝ) p.1 p.2) ∂(μ.prod (law n))) =
                    (∫ x : Fin (n + 1) → ℝ, f x ∂law (n + 1)) := by
    calc
      (∫ p : ℝ × (Fin n → ℝ), f (Fin.cons (α := fun _ => ℝ) p.1 p.2) ∂(μ.prod (law n))) =
          (∫ p : ℝ × (Fin n → ℝ), f (e.symm p) ∂(μ.prod (law n))) := by
        apply integral_congr_ae
        filter_upwards with p
        simp [h_symm_eq p]
      _ = (∫ x : Fin (n + 1) → ℝ, f x ∂law (n + 1)) := h_int_comp
  have h_int_prod : (∫ p : ℝ × (Fin n → ℝ), f (Fin.cons (α := fun _ => ℝ) p.1 p.2) ∂(μ.prod (law n))) =
                   (∫ a : ℝ, (∫ y : Fin n → ℝ, f (Fin.cons (α := fun _ => ℝ) a y) ∂law n) ∂μ) := by
    have h_int : Integrable (fun (p : ℝ × (Fin n → ℝ)) => f (Fin.cons (α := fun _ => ℝ) p.1 p.2)) (μ.prod (law n)) := by
      have h_int' : Integrable (f ∘ e.symm) (μ.prod (law n)) :=
        h_mp_symm.integrable_comp_of_integrable hf
      have h_eq : (f ∘ e.symm) = (fun (p : ℝ × (Fin n → ℝ)) => f (Fin.cons (α := fun _ => ℝ) p.1 p.2)) := by
        ext p
        simp [h_symm_eq p]
      rw [h_eq] at h_int'
      exact h_int'
    rw [integral_prod _ h_int]
  calc
    (∫ x : Fin (n + 1) → ℝ, f x ∂law (n + 1)) =
        (∫ p : ℝ × (Fin n → ℝ), f (Fin.cons (α := fun _ => ℝ) p.1 p.2) ∂(μ.prod (law n))) := by
      rw [h_int_comp']
    _ = (∫ a : ℝ, (∫ y : Fin n → ℝ, f (Fin.cons (α := fun _ => ℝ) a y) ∂law n) ∂μ) := by
      rw [h_int_prod]
    _ = (∫ a in Set.Icc (0 : ℝ) 1, (∫ y : Fin n → ℝ, f (Fin.cons (α := fun _ => ℝ) a y) ∂law n)) := rfl

theorem lintegral_law_succ_snoc {n : ℕ} (f : (Fin (n + 1) → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂law (n + 1) =
      ∫⁻ y, (∫⁻ a in Set.Icc (0 : ℝ) 1, f (Fin.snoc (α := fun _ => ℝ) y a)) ∂law n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hmp : MeasurePreserving e (law (n + 1))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law n)) := by
    simpa [e, law] using measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => volume.restrict (Set.Icc (0 : ℝ) 1)) (Fin.last n)
  have h_symm_apply (a : ℝ) (y : Fin n → ℝ) : e.symm (a, y) = Fin.snoc y a := by
    ext x
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last, Fin.snocEquiv_apply]
  have h1 : ∫⁻ x, f x ∂law (n + 1) = ∫⁻ p, f (e.symm p) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law n)) := by
    simpa [Function.comp] using (hmp.lintegral_map_equiv (f ∘ e.symm) e).symm
  have h_meas : Measurable (f ∘ e.symm) := hf.comp e.symm.measurable
  have h2 : ∫⁻ p, f (e.symm p) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law n)) =
      ∫⁻ y, ∫⁻ a, f (e.symm (a, y)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂(law n) := by
    have : (fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) = f ∘ e.symm := rfl
    rw [this]
    rw [lintegral_prod_symm' (f ∘ e.symm) h_meas]
    rfl
  calc
    ∫⁻ x, f x ∂law (n + 1)
        = ∫⁻ p, f (e.symm p) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law n)) := h1
    _ = ∫⁻ y, ∫⁻ a, f (e.symm (a, y)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂(law n) := h2
    _ = ∫⁻ y, (∫⁻ a in Set.Icc (0 : ℝ) 1, f (Fin.snoc y a)) ∂(law n) := by
      simp_rw [h_symm_apply]

theorem integral_coord {n : ℕ} (j : Fin n) : ∫ x, x j ∂law n = 1 / 2 := by
  unfold law
  have h_ae : AEStronglyMeasurable (fun (a : ℝ) => a) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (continuous_id.measurable).aestronglyMeasurable
  have h := MeasureTheory.integral_comp_eval (μ := fun (_ : Fin n) => volume.restrict (Set.Icc (0 : ℝ) 1))
    (f := fun (a : ℝ) => a) (i := j) h_ae
  rw [h]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_id]
  norm_num

end Robbins
