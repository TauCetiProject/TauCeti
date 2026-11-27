/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.Variational.FormEigenspace.Basic
import TauCeti.Analysis.InnerProductSpace.Variational.Shift
import TauCeti.Topology.Algebra.Module.Span

/-!
# Successive Rayleigh minima of a compact form pair

Minimize the energy of a compact form pair on unit vectors perpendicular, in the ambient
Hilbert space, to the images of the eigenvectors already chosen. A finite span of these
images admits an orthogonal projection, and that projection takes values in the form-domain
image. This allows one to split the weak eigen-equation into the equation on the
orthogonal complement and the equation on the previous span.
The complement equation uses the constrained Euler–Lagrange theorem
`TauCeti.CompactFormPair.form_apply_eq_mul_inner_of_isMinOn`.

Compactness forces the energies of the resulting orthonormal family to diverge in infinite
dimension. In the shifted coercive energy space, any vector orthogonal to every minimizer
would provide a fixed Rayleigh quotient bounding all those energies, so the minimizers span
a dense subspace of the form domain. Their images therefore form a Hilbert basis, and the
vectors at each energy span the corresponding variational eigenspace.

## References

* V. Ivrii, *Partial Differential Equations*, Chapter 13, §13.1, Theorem 4 and its proof.
-/

public section

open Set Submodule ContinuousLinearMap RCLike Filter
open scoped InnerProductSpace

namespace TauCeti.CompactFormPair

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : CompactFormPair 𝕜 V H)

section FiniteSpan

variable {s : Set V}

private theorem form_apply_eq_mul_inner_of_mem_span {u : V} {lam : ℝ}
    (hu : P.inclusion u ∈ (span 𝕜 (P.inclusion '' s))ᗮ)
    (heig : ∀ w ∈ s, ∃ μ, w ∈ P.formEigenspace μ) {v : V} (hv : v ∈ span 𝕜 s) :
    P.form u v = (lam : 𝕜) * inner 𝕜 (P.inclusion u) (P.inclusion v) := by
  have hker : span 𝕜 s ≤ (shiftedForm P.inclusion P.form (-lam) u).toLinearMap.ker := by
    refine Submodule.span_le.2 fun w hw ↦ ?_
    obtain ⟨μ, he⟩ := heig w hw
    have hwu := inner_right_of_mem_orthogonal
      (subset_span (mem_image_of_mem P.inclusion hw)) hu
    have huw := inner_left_of_mem_orthogonal
      (subset_span (mem_image_of_mem P.inclusion hw)) hu
    apply LinearMap.mem_ker.2
    simp only [coe_coe, shiftedForm_apply, P.hermitian u w, mem_formEigenspace.1 he u,
      huw, hwu, mul_zero, star_zero, add_zero]
  simpa only [coe_coe, shiftedForm_apply, ofReal_neg, neg_mul, ← sub_eq_add_neg, sub_eq_zero]
    using LinearMap.mem_ker.1 (hker hv)

/-- A Rayleigh minimizer perpendicular to a finite family of variational eigenvectors
satisfies the full weak eigen-equation at its energy. -/
theorem mem_formEigenspace_energy_of_isMinOn_orthogonal_span (hs : s.Finite)
    (heig : ∀ w ∈ s, ∃ μ, w ∈ P.formEigenspace μ) {u : V}
    (hu : u ∈ P.unitConstraint (span 𝕜 (P.inclusion '' s))ᗮ)
    (hmin : IsMinOn P.energy (P.unitConstraint (span 𝕜 (P.inclusion '' s))ᗮ) u) :
    u ∈ P.formEigenspace (P.energy u) := by
  refine mem_formEigenspace.2 fun v ↦ ?_
  obtain ⟨w, hw, z, hz, rfl⟩ := P.exists_add_mem_span_inclusion_mem_orthogonal hs v
  have hsub := form_apply_eq_mul_inner_of_isMinOn hu hmin hz
  have hspan := P.form_apply_eq_mul_inner_of_mem_span (lam := P.energy u)
    (mem_unitConstraint.1 hu).1 heig hw
  simp only [map_add, inner_add_right, mul_add, hspan, hsub]

end FiniteSpan

section Construction

open Cardinal

-- Values beyond the dimension of a finite-dimensional target are never used.
private noncomputable def successiveMinimizer (P : CompactFormPair 𝕜 V H) (n : ℕ) : V := by
  classical
  let s := range fun i : Iio n ↦ successiveMinimizer P i
  let S := P.unitConstraint (span 𝕜 (P.inclusion '' s))ᗮ
  exact if h : ∃ u ∈ S, IsMinOn P.energy S u then h.choose else 0
termination_by n
decreasing_by exact i.property

variable [CompleteSpace V]

private theorem successiveMinimizer_spec (n : ℕ) (hn : (n : Cardinal) < Module.rank 𝕜 H) :
    let u := P.successiveMinimizer
    let S := P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio n))ᗮ
    u n ∈ S ∧ IsMinOn P.energy S (u n) ∧ u n ∈ P.formEigenspace (P.energy (u n)) := by
  dsimp only
  induction n using Nat.strongRecOn with
  | ind n ih =>
    let u := P.successiveMinimizer
    let s := u '' Iio n
    let W := span 𝕜 (P.inclusion '' s)
    have hs : s.Finite := (finite_Iio n).image _
    have hW : W ≠ ⊤ := by
      classical
      let t := (Finset.Iio n).image (P.inclusion ∘ u)
      have ht : (t : Set H) = P.inclusion '' s := by
        simp only [t, s, Finset.coe_image, Finset.coe_Iio, Set.image_comp]
      have hrank : Module.rank 𝕜 W ≤ (n : Cardinal) := calc
        _ = Module.rank 𝕜 (span 𝕜 (t : Set H)) :=
          congrArg (fun r : Set H ↦ Module.rank 𝕜 (span 𝕜 r)) ht.symm
        _ ≤ (t.card : Cardinal) := rank_span_finset_le (R := 𝕜) t
        _ ≤ (n : Cardinal) := Nat.cast_le.2 (Finset.card_image_le.trans_eq (Nat.card_Iio n))
      intro h
      rw [h, rank_top] at hrank
      exact hn.not_ge hrank
    have hmin : ∃ w ∈ P.unitConstraint Wᗮ, IsMinOn P.energy (P.unitConstraint Wᗮ) w :=
      P.exists_isMinOn_energy_unitConstraint _ W.isClosed_orthogonal
        (P.unitConstraint_orthogonal_span_nonempty hs hW)
    have hu : u n ∈ P.unitConstraint Wᗮ ∧ IsMinOn P.energy (P.unitConstraint Wᗮ) (u n) := by
      have heq : u n = hmin.choose := by
        dsimp only [u]
        rw [successiveMinimizer, ← image_eq_range]
        exact dite_eq_left hmin
      rw [heq]
      exact hmin.choose_spec
    have heig : ∀ w ∈ s, ∃ μ, w ∈ P.formEigenspace μ := by
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨_, (ih m hm ((Nat.cast_lt.2 hm).trans hn)).2.2⟩
    simpa only [image_comp] using
      ⟨hu.1, hu.2, P.mem_formEigenspace_energy_of_isMinOn_orthogonal_span hs heig hu.1 hu.2⟩

omit [CompleteSpace V] in
private theorem orthonormal_monotone_of_successive_minima {ι : Type*} [LinearOrder ι]
    {u : ι → V}
    (h : ∀ i,
      u i ∈ P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio i))ᗮ ∧
      IsMinOn P.energy (P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio i))ᗮ) (u i)) :
    Orthonormal 𝕜 (P.inclusion ∘ u) ∧ Monotone (P.energy ∘ u) := by
  refine ⟨⟨fun i ↦ (mem_unitConstraint.1 (h i).1).2, ?_⟩, ?_⟩
  · have horth (i j : ι) (hij : i < j) :
        inner 𝕜 (P.inclusion (u i)) (P.inclusion (u j)) = 0 :=
      inner_right_of_mem_orthogonal (subset_span (mem_image_of_mem (P.inclusion ∘ u) hij))
        (mem_unitConstraint.1 (h j).1).1
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact horth i j hlt
    · exact inner_eq_zero_symm.1 (horth j i hgt)
  · intro i j hij
    exact (h i).2 (unitConstraint_mono (orthogonal_le (span_mono (image_mono (Iio_subset_Iio hij))))
      (h j).1)

/-- In infinite dimension, successive constrained minima give orthonormal form-domain images
and a nondecreasing sequence of variational eigenvalues equal to the energies of the minimizers.
Each minimizer is on the unit constraint perpendicular to all its predecessors. -/
theorem exists_successive_minimizers (hH : ¬ FiniteDimensional 𝕜 H) :
    ∃ u : ℕ → V, Orthonormal 𝕜 (P.inclusion ∘ u) ∧ Monotone (P.energy ∘ u) ∧
      (∀ n, u n ∈ P.formEigenspace (P.energy (u n))) ∧
      ∀ n, u n ∈ P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio n))ᗮ ∧
        IsMinOn P.energy (P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio n))ᗮ) (u n) := by
  have hr : ℵ₀ ≤ Module.rank 𝕜 H := le_of_not_gt (fun h ↦ hH (Module.rank_lt_aleph0_iff.1 h))
  have h (n : ℕ) := P.successiveMinimizer_spec n ((natCast_lt_aleph0 (n := n)).trans_le hr)
  have hmin n := And.intro (h n).1 (h n).2.1
  obtain ⟨hon, hmono⟩ := P.orthonormal_monotone_of_successive_minima hmin
  exact ⟨P.successiveMinimizer, hon, hmono, fun n ↦ (h n).2.2, hmin⟩

omit [CompleteSpace V] in
/-- In finite dimension, successive constrained minima give an orthonormal eigenbasis of
the ambient space, ordered by the energies of its form-domain representatives. -/
theorem exists_ordered_orthonormalBasis [FiniteDimensional 𝕜 H] :
    ∃ (u : Fin (Module.finrank 𝕜 H) → V)
      (b : OrthonormalBasis (Fin (Module.finrank 𝕜 H)) 𝕜 H),
      (⇑b = P.inclusion ∘ u) ∧ Monotone (P.energy ∘ u) ∧
      (∀ i, u i ∈ P.formEigenspace (P.energy (u i))) ∧
      ∀ i, u i ∈ P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio i))ᗮ ∧
        IsMinOn P.energy (P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio i))ᗮ) (u i) := by
  let : FiniteDimensional 𝕜 V := FiniteDimensional.of_injective P.inclusion.toLinearMap P.injective
  let : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  let u : Fin (Module.finrank 𝕜 H) → V := fun i ↦ P.successiveMinimizer i
  have h (i : Fin (Module.finrank 𝕜 H)) := P.successiveMinimizer_spec i
    (Module.finrank_eq_rank 𝕜 H ▸ (Nat.cast_lt (α := Cardinal)).2 i.isLt)
  have hspan (i : Fin (Module.finrank 𝕜 H)) :
      (P.inclusion ∘ u) '' Iio i = (P.inclusion ∘ P.successiveMinimizer) '' Iio (i : ℕ) := by
    calc
      _ = ((P.inclusion ∘ P.successiveMinimizer) ∘ Fin.val) '' Iio i := rfl
      _ = _ := by rw [Set.image_comp, Fin.image_val_Iio]
  have hmin (i : Fin (Module.finrank 𝕜 H)) :
      u i ∈ P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio i))ᗮ ∧
        IsMinOn P.energy (P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio i))ᗮ) (u i) := by
    rw [hspan i]
    exact ⟨(h i).1, (h i).2.1⟩
  obtain ⟨hon, hmono⟩ := P.orthonormal_monotone_of_successive_minima hmin
  have htop := hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  exact ⟨u, OrthonormalBasis.mk hon htop.ge, OrthonormalBasis.coe_mk hon htop.ge, hmono,
    fun i ↦ (h i).2.2, hmin⟩

end Construction

section Completeness

variable [CompleteSpace V]

/-- A sequence of successive variational eigenvectors with unit orthonormal images spans
a dense subspace of the form domain. -/
theorem dense_span_of_successive_minima {u : ℕ → V} (hon : Orthonormal 𝕜 (P.inclusion ∘ u))
    (heig : ∀ n, u n ∈ P.formEigenspace (P.energy (u n)))
    (hmin : ∀ n, IsMinOn P.energy (P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio n))ᗮ) (u n)) :
    Dense (span 𝕜 (range u) : Set V) := by
  obtain ⟨c, hc, ω, hcoer⟩ := P.exists_mul_norm_sq_le_energy_add
  let a := CoerciveHermitianForm.ofSemibounded P.form P.inclusion P.hermitian hc
    (fun v ↦ by simpa only [← P.energy_def v] using hcoer v) ω le_rfl
  let S := span 𝕜 (range (a.toEnergySpace ∘ u))
  have hdiv : Tendsto (P.energy ∘ u) atTop atTop :=
    Nat.cofinite_eq_atTop ▸ P.tendsto_cofinite_energy_of_orthonormal hon
  have hperp : Sᗮ = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ (Submodule.mem_bot 𝕜).2 ?_
    let v := a.toEnergySpace.symm x
    have hxv : a.toEnergySpace v = x := a.toEnergySpace.apply_symm_apply x
    have horth (n : ℕ) : inner 𝕜 (P.inclusion (u n)) (P.inclusion v) = 0 := by
      have hn : u n ≠ 0 := fun h ↦ by simpa [Function.comp_apply, h] using hon.1 n
      have hne : P.formEigenspace (P.energy (u n)) ≠ ⊥ := fun h ↦ hn (by simpa [h] using heig n)
      have hpos := neg_lt_of_formEigenspace_ne_bot hc hcoer hne
      have he : inner 𝕜 (a.toEnergySpace (u n)) (a.toEnergySpace v) = 0 := by
        rw [hxv]
        exact inner_right_of_mem_orthogonal (subset_span (mem_range_self n)) hx
      have heq : inner 𝕜 (a.toEnergySpace (u n)) (a.toEnergySpace v) =
          ((P.energy (u n) + ω : ℝ) : 𝕜) * inner 𝕜 (P.inclusion (u n)) (P.inclusion v) := by
        rw [a.inner_toEnergySpace, CoerciveHermitianForm.ofSemibounded_form, shiftedForm_apply]
        simp only [mem_formEigenspace.1 (heig n) v, ofReal_add, add_mul]
      exact (mul_eq_zero.1 (heq.symm.trans he)).resolve_left (ofReal_ne_zero.2 (by linarith))
    by_contra hx0
    have hv0 : v ≠ 0 := fun hz ↦ hx0 (by simpa [hz] using hxv.symm)
    have hj : 0 < ‖P.inclusion v‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (fun h ↦ hv0 (P.injective (h.trans (map_zero _).symm)))) 2
    have hbound (n : ℕ) : P.energy (u n) ≤ P.energy v / ‖P.inclusion v‖ ^ 2 := by
      refine (le_div_iff₀ hj).2 (mul_norm_sq_le_energy_of_isMinOn (hmin n) ?_)
      refine (mem_orthogonalBilin_span (B := innerₛₗ 𝕜)).2 ?_
      rintro _ ⟨k, _, rfl⟩
      exact horth k
    obtain ⟨n, hn⟩ := (tendsto_atTop.1 hdiv (P.energy v / ‖P.inclusion v‖ ^ 2 + 1)).exists
    exact (not_le_of_gt (lt_add_one _)) (hn.trans (hbound n))
  have hS : Dense (S : Set a.EnergySpace) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← orthogonal_orthogonal_eq_closure,
      hperp, bot_orthogonal_eq_top]
  let e := a.toEnergySpace
  have hcomp : e.symm ∘ (e ∘ u) = u := funext fun n ↦ e.symm_apply_apply (u n)
  have hmap : Dense (span 𝕜 (range (e.symm ∘ (e ∘ u))) : Set V) :=
    e.symm.surjective.denseRange.dense_span_range_comp
      (f := e.symm.toLinearEquiv.toLinearMap) e.symm.continuous hS
  simpa only [hcomp] using hmap

/-- In infinite dimension, successive Rayleigh minimizers have a nondecreasing sequence of
eigenvalues tending to infinity, and their images form a Hilbert basis of the ambient space. -/
theorem exists_ordered_eigenbasis [CompleteSpace H] (hH : ¬ FiniteDimensional 𝕜 H) :
    ∃ (u : ℕ → V) (b : HilbertBasis ℕ 𝕜 H),
      (⇑b = P.inclusion ∘ u) ∧ Monotone (P.energy ∘ u) ∧ Tendsto (P.energy ∘ u) atTop atTop ∧
      (∀ n, u n ∈ P.formEigenspace (P.energy (u n))) ∧
      ∀ n, u n ∈ P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio n))ᗮ ∧
        IsMinOn P.energy (P.unitConstraint (span 𝕜 ((P.inclusion ∘ u) '' Iio n))ᗮ) (u n) := by
  obtain ⟨u, hon, hmono, heig, hmin⟩ := P.exists_successive_minimizers hH
  have hd := P.dense_span_of_successive_minima hon heig (fun n ↦ (hmin n).2)
  have hJ := P.denseRange.dense_span_range_comp (f := P.inclusion.toLinearMap)
    P.inclusion.continuous hd
  have htop : ⊤ ≤ (span 𝕜 (range (P.inclusion ∘ u))).topologicalClosure := by
    exact (Submodule.dense_iff_topologicalClosure_eq_top.1 hJ).ge
  have hdiv : Tendsto (P.energy ∘ u) atTop atTop :=
    Nat.cofinite_eq_atTop ▸ P.tendsto_cofinite_energy_of_orthonormal hon
  exact ⟨u, HilbertBasis.mk hon htop, HilbertBasis.coe_mk hon htop, hmono, hdiv, heig, hmin⟩

end Completeness

end TauCeti.CompactFormPair
