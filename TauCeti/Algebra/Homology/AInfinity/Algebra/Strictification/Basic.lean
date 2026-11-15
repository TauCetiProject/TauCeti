/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.CohomologicalUnit
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology
public import TauCeti.Algebra.Module.GradedModule.Dual.Basic
-- Private: the limit constructions, the inductive gauge step, and projective dual extensions are
-- implementation details of the strictification proofs and do not appear in exported signatures.
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Limit
import TauCeti.Algebra.Homology.AInfinity.Algebra.Limit
import TauCeti.Algebra.Homology.AInfinity.Algebra.Strictification.UnitKilling

/-!
# Keller's unit strictification for `A∞` algebras

Every strict unit of an `A∞` algebra is a cohomological unit, and cohomological unitality is
invariant under `A∞` quasi-isomorphism.  Over a field the converse holds up to quasi-isomorphism
(**Keller's unit strictification**): every cohomologically unital `A∞` algebra is quasi-isomorphic
to a strictly unital minimal `A∞` algebra on its cohomology.

The proof has two halves:

1. **Minimal unit strictification along a degree-zero retraction**
   (`IsMinimal.exists_strictUnit_isIso_of_mem_dualPiece`), valid over any commutative ring `R`.
   Given a minimal `A∞` algebra `𝒜`, a cohomological unit `e`, and a degree-zero linear functional
   `π ∈ 𝒜.grading.dualPiece 0` with `π e = 1`, iterating the single-arity gauge step
   `IsMinimal.exists_strictUnit_step_of_mem_dualPiece` produces a sequence of minimal `A∞`
   structures and comparison `A∞` isomorphisms with identity linear part whose Taylor components
   stabilise in each filtration degree.  Passing to the limits `AInfinityAlgebra.limit` and
   `AInfinityHom.limit` yields a minimal `A∞` structure `𝒜'` on the same graded module with the
   same binary product `m₂`, for which `e` is a strict unit, together with an `A∞` isomorphism
   `f : 𝒜' ⟶ 𝒜` with `f₁ = id`.
2. **Passage to a field and homological transfer** (`IsMinimal.exists_strictUnit_isIso` and
   `CohomologicalUnit.exists_strictUnit_minimalModel`).  Over a field `K`, if `e = 0` on a minimal
   algebra then `𝒜` is already zero (`IsMinimal.strictUnit_zero_of_cohomologicalUnit_zero`); if
   `e ≠ 0`, `Module.Projective.exists_dual_eq_one` on the degree-zero piece supplies the required
   retraction `π ∈ 𝒜.grading.dualPiece 0`.  For a general cohomologically unital `A∞` algebra `𝒜`
   over `K`, Kadeishvili's minimal model `𝒜.minimalModel` on `H*(𝒜)` inherits the cohomology unit
   class `[e]`, and strictifying `𝒜.minimalModel` produces a strictly unital minimal model `ℋ` on
   `H*(𝒜)` together with quasi-isomorphisms `i : ℋ ⟶ 𝒜` and `p : 𝒜 ⟶ ℋ` satisfying `p ∘ i = id`.

Consequently, over a field an `A∞` algebra is cohomologically unital if and only if it admits a
quasi-isomorphism from (or to) a strictly unital `A∞` algebra
(`cohomologicallyUnital_iff_exists_strictUnit_isQuasiIso` and
`cohomologicallyUnital_iff_exists_strictUnit_isQuasiIso_from`).

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.strictUnit_iff_taylor_of_tprod_eq_zero`: on a minimal `A∞`
  algebra, strict units are cohomological units killed by `taylor` in arities `k ≠ 2`.
* `TauCeti.AInfinityAlgebra.IsMinimal.exists_strictUnit_isIso_of_mem_dualPiece`: minimal unit
  strictification over a commutative ring given a degree-zero retraction `π e = 1`.
* `TauCeti.AInfinityAlgebra.IsMinimal.exists_strictUnit_isIso`: minimal unit strictification over a
  field.
* `TauCeti.AInfinityAlgebra.CohomologicalUnit.exists_strictUnit_minimalModel`: Keller's unit
  strictification theorem, producing a strictly unital minimal model on cohomology.
* `TauCeti.AInfinityAlgebra.cohomologicallyUnital_iff_exists_strictUnit_isQuasiIso` and
  `TauCeti.AInfinityAlgebra.cohomologicallyUnital_iff_exists_strictUnit_isQuasiIso_from`: over a
  field, cohomological unitality is equivalent to being quasi-isomorphic to a strictly unital `A∞`
  algebra.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Homology Homotopy Appl. 3 (2001),
  1--35, Sections 3.1, 3.3, and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Ph.D. thesis, Université Paris 7 (2003),
  Chapter 3, Section 3.2.
* P. Seidel, *Fukaya Categories and Picard--Lefschetz Theory*, Zurich Lectures in Advanced
  Mathematics (2008), Chapter I, Section 2.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uK uA

/-! ### Minimal unit strictification over a commutative ring -/

section CommRing

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- On a minimal `A∞` algebra, a cohomological unit `e` is a strict unit as soon as the suspended
Taylor map vanishes on every pure tensor word of length `k ≠ 2` containing `e`. -/
theorem IsMinimal.strictUnit_of_taylor_of_tprod_eq_zero {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e)
    (h : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0) :
    𝒜.StrictUnit e where
  degree_zero := he.degree_zero
  binary_left := h𝒜.cohomologicalUnit_binary_left he
  binary_right := h𝒜.cohomologicalUnit_binary_right he
  higher n hn x := by
    rintro ⟨i, hi⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [m_zero, zero_apply]
    have hyi : 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i) = e := by
      rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero he.degree_zero]
    have hz := h ⟨n, hn0⟩ hn (fun r ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - r) (x r)) ⟨i, hyi⟩
    rw [taylor_of_tprod] at hz
    simpa only [InternalGrading.koszulTwist_koszulTwist] using hz

/-- On a minimal `A∞` algebra, `e` is a strict unit if and only if it is a cohomological unit and
`𝒜.taylor` vanishes on pure tensor words of length `k ≠ 2` containing `e`. -/
theorem IsMinimal.strictUnit_iff_taylor_of_tprod_eq_zero {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} :
    𝒜.StrictUnit e ↔ 𝒜.CohomologicalUnit e ∧
      ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → ∀ x : Fin k.1 → A,
        (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0 :=
  ⟨fun h ↦ ⟨h.cohomologicalUnit, h.taylor_of_tprod_eq_zero⟩,
   fun ⟨he, h⟩ ↦ h𝒜.strictUnit_of_taylor_of_tprod_eq_zero he h⟩

/-- Stage `m` of minimal unit strictification: a minimal `A∞` structure with the grading and binary
operation of `𝒜`, in which `e` is killed by `taylor` in all arities `k ≠ 2` up to `m + 2`, together
with a comparison `A∞` isomorphism to `𝒜` with identity linear part. -/
private structure StrictificationStage (𝒜 : AInfinityAlgebra R A) (e : A) (m : ℕ) where
  alg : AInfinityAlgebra R A
  grading_eq : alg.grading = 𝒜.grading
  isMinimal : alg.IsMinimal
  m_two_eq : alg.m 2 = 𝒜.m 2
  taylor_eq_zero : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
    (∃ r, x r = e) → alg.taylor (of R A k (PiTensorProduct.tprod R x)) = 0
  hom : AInfinityHom alg 𝒜
  isIso_hom : hom.IsIso
  linearPart_hom : hom.linearPart = LinearMap.id

private theorem exists_strictificationStage_succ {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπ : π ∈ 𝒜.grading.dualPiece 0) (hπe : π e = 1) {m : ℕ}
    (s : StrictificationStage 𝒜 e m) :
    ∃ s' : StrictificationStage 𝒜 e (m + 1),
      (∀ z ∈ filtration R A (m + 2), s'.alg.taylor z = s.alg.taylor z) ∧
      (∀ z ∈ filtration R A (m + 1), s'.hom.taylor z = s.hom.taylor z) := by
  have he_s : s.alg.CohomologicalUnit e :=
    s.isMinimal.cohomologicalUnit_iff.2 ⟨s.grading_eq.symm ▸ he.degree_zero,
      fun x ↦ by rw [s.m_two_eq, h𝒜.cohomologicalUnit_binary_left he],
      fun x ↦ by rw [s.m_two_eq, h𝒜.cohomologicalUnit_binary_right he]⟩
  obtain ⟨𝒜', g, hG', hmin', htay', hzero', hg_filt, hg_iso, hg_lin⟩ :=
    s.isMinimal.exists_strictUnit_step_of_mem_dualPiece he_s (s.grading_eq.symm ▸ hπ) hπe m
      s.taylor_eq_zero
  have hm2' : 𝒜'.m 2 = 𝒜.m 2 := MultilinearMap.ext fun x ↦ by
    have h := htay' _ (filtration_monotone R A (by omega : 2 ≤ m + 2)
      (of_mem_filtration R A (k := ⟨2, two_pos⟩) le_rfl (PiTensorProduct.tprod R fun i ↦
        s.alg.grading.koszulTwist (((2 : ℕ) : ℤ) - 1 - i) (x i))))
    rw [taylor_of_tprod, taylor_of_tprod, hG'] at h
    have h2 : 𝒜'.m 2 x = s.alg.m 2 x := by
      simpa only [InternalGrading.koszulTwist_koszulTwist] using h
    rw [h2, s.m_two_eq]
  refine ⟨⟨𝒜', hG'.trans s.grading_eq, hmin', hm2', hzero', s.hom.comp g,
    s.isIso_hom.comp hg_iso,
    by rw [AInfinityHom.linearPart_comp, hg_lin, s.linearPart_hom, LinearMap.comp_id]⟩,
    htay', fun z hz ↦ ?_⟩
  have hbar : g.barMap z = z :=
    g.isCoalgHom_barMap.apply_eq_of_mem_filtration (isCoalgHom_id A)
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply, ← AInfinityHom.taylor_def, hg_filt w hw, LinearMap.id_apply])
      hz
  rw [AInfinityHom.taylor_comp, LinearMap.comp_apply, hbar]

private noncomputable def strictificationStage {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπ : π ∈ 𝒜.grading.dualPiece 0) (hπe : π e = 1) :
    (m : ℕ) → StrictificationStage 𝒜 e m
  | 0 =>
    { alg := 𝒜
      grading_eq := rfl
      isMinimal := h𝒜
      m_two_eq := rfl
      taylor_eq_zero := fun ⟨kval, hkpos⟩ hk2 hkle _ _ ↦ by
        dsimp only at hk2 hkle
        obtain rfl : kval = 1 := by omega
        rw [taylor_of_tprod, h𝒜.m_one]
      hom := AInfinityHom.id 𝒜
      isIso_hom := AInfinityHom.isIso_id 𝒜
      linearPart_hom := AInfinityHom.linearPart_id 𝒜 }
  | m + 1 =>
    Classical.choose (exists_strictificationStage_succ h𝒜 he hπ hπe
      (strictificationStage h𝒜 he hπ hπe m))

/-- **Minimal unit strictification along a degree-zero retraction.**  Let `𝒜` be a minimal `A∞`
algebra over a commutative ring `R`, let `e` be a cohomological unit of `𝒜`, and let
`π ∈ 𝒜.grading.dualPiece 0` be a degree-zero linear functional with `π e = 1`.  Then there exist a
minimal `A∞` structure `𝒜'` on the same graded module with `𝒜'.m 2 = 𝒜.m 2` for which `e` is a
strict unit, and an `A∞` isomorphism `f : 𝒜' ⟶ 𝒜` with `f.linearPart = id`. -/
theorem IsMinimal.exists_strictUnit_isIso_of_mem_dualPiece {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπ : π ∈ 𝒜.grading.dualPiece 0) (hπe : π e = 1) :
    ∃ (𝒜' : AInfinityAlgebra R A) (f : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧ 𝒜'.m 2 = 𝒜.m 2 ∧
      𝒜'.StrictUnit e ∧ f.IsIso ∧ f.linearPart = LinearMap.id := by
  let s := strictificationStage h𝒜 he hπ hπe
  have hstab_alg : ∀ m, ∀ z ∈ filtration R A m,
      (s (m + 1)).alg.taylor z = (s m).alg.taylor z := fun m z hz ↦
    (Classical.choose_spec (exists_strictificationStage_succ h𝒜 he hπ hπe (s m))).1 z
      (filtration_monotone R A (by omega : m ≤ m + 2) hz)
  have hstab_hom : ∀ m, ∀ z ∈ filtration R A m,
      (s (m + 1)).hom.taylor z = (s m).hom.taylor z := fun m z hz ↦
    (Classical.choose_spec (exists_strictificationStage_succ h𝒜 he hπ hπe (s m))).2 z
      (filtration_monotone R A m.le_succ hz)
  let 𝒜' := limit (fun m ↦ (s m).alg) (fun m ↦ (s m).grading_eq) hstab_alg
  have hG' : 𝒜'.grading = 𝒜.grading := limit_grading (fun m ↦ (s m).grading_eq) hstab_alg
  have hmin' : 𝒜'.IsMinimal :=
    (isMinimal_limit_iff (fun m ↦ (s m).grading_eq) hstab_alg).2 (s 1).isMinimal
  have hm2' : 𝒜'.m 2 = 𝒜.m 2 :=
    (m_limit (fun m ↦ (s m).grading_eq) hstab_alg 2).trans (s 2).m_two_eq
  have he' : 𝒜'.CohomologicalUnit e :=
    hmin'.cohomologicalUnit_iff.2 ⟨hG'.symm ▸ he.degree_zero,
      fun x ↦ by rw [hm2', h𝒜.cohomologicalUnit_binary_left he],
      fun x ↦ by rw [hm2', h𝒜.cohomologicalUnit_binary_right he]⟩
  have hstr' : 𝒜'.StrictUnit e :=
    hmin'.strictUnit_of_taylor_of_tprod_eq_zero he' fun k hk2 x hx ↦ by
      rw [taylor_limit_apply_of_mem_filtration (fun m ↦ (s m).grading_eq) hstab_alg
        (of_mem_filtration R A (k := k) le_rfl _)]
      exact (s k.1).taylor_eq_zero k hk2 (by omega) x hx
  have h𝒜'_eq : ∀ m, ∀ z ∈ filtration R A m, (s m).alg.taylor z = 𝒜'.taylor z :=
    fun m z hz ↦ (taylor_limit_apply_of_mem_filtration (fun m ↦ (s m).grading_eq) hstab_alg hz).symm
  let f := AInfinityHom.limit (fun m ↦ (s m).hom)
    (fun m ↦ ((s m).grading_eq).trans hG'.symm) h𝒜'_eq hstab_hom
  refine ⟨𝒜', f, hG', hmin', hm2', hstr', ?_, ?_⟩
  · exact (AInfinityHom.isIso_limit_iff hstab_hom _ h𝒜'_eq).2 (s 1).isIso_hom
  · rw [AInfinityHom.linearPart_limit hstab_hom _ h𝒜'_eq, (s 1).linearPart_hom]

end CommRing

/-! ### Keller's unit strictification over a field -/

section Field

variable {K : Type uK} {A : Type uA} [Field K] [AddCommGroup A] [Module K A]

/-- **Minimal unit strictification over a field.**  Every minimal `A∞` algebra `𝒜` over a field `K`
with a cohomological unit `e` is `A∞` isomorphic, via a morphism with identity linear part, to a
minimal `A∞` structure `𝒜'` on the same graded vector space with `𝒜'.m 2 = 𝒜.m 2` for which `e` is
a strict unit. -/
theorem IsMinimal.exists_strictUnit_isIso {𝒜 : AInfinityAlgebra K A} (h𝒜 : 𝒜.IsMinimal) {e : A}
    (he : 𝒜.CohomologicalUnit e) :
    ∃ (𝒜' : AInfinityAlgebra K A) (f : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧ 𝒜'.m 2 = 𝒜.m 2 ∧
      𝒜'.StrictUnit e ∧ f.IsIso ∧ f.linearPart = LinearMap.id := by
  by_cases hne : e = 0
  · subst hne
    exact ⟨𝒜, AInfinityHom.id 𝒜, rfl, h𝒜, rfl, h𝒜.strictUnit_zero_of_cohomologicalUnit_zero he,
      AInfinityHom.isIso_id 𝒜, AInfinityHom.linearPart_id 𝒜⟩
  · have he₀ : e ∈ 𝒜.grading.piece (-0) := by simpa only [neg_zero] using he.degree_zero
    obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one K (x := (⟨e, he₀⟩ : 𝒜.grading.piece _))
      (by simpa [← Subtype.coe_ne_coe] using hne)
    let π := (𝒜.grading.dualPieceEquiv 0).symm φ₀
    have hπe : (π : Module.Dual K A) e = 1 :=
      (𝒜.grading.dualPieceEquiv_symm_apply_coe 0 φ₀ ⟨e, he₀⟩).trans hφ₀
    exact h𝒜.exists_strictUnit_isIso_of_mem_dualPiece he π.2 hπe

/-- Every minimal cohomologically unital `A∞` algebra over a field is `A∞` isomorphic, via a
morphism with identity linear part, to a strictly unital minimal `A∞` structure on the same graded
vector space with the same binary operation. -/
theorem IsMinimal.exists_strictUnit_isIso_of_cohomologicallyUnital {𝒜 : AInfinityAlgebra K A}
    (h𝒜 : 𝒜.IsMinimal) (hu : 𝒜.CohomologicallyUnital) :
    ∃ (e : A) (𝒜' : AInfinityAlgebra K A) (f : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧ 𝒜'.m 2 = 𝒜.m 2 ∧
      𝒜'.StrictUnit e ∧ f.IsIso ∧ f.linearPart = LinearMap.id := by
  obtain ⟨e, he⟩ := (cohomologicallyUnital_def 𝒜).1 hu
  obtain ⟨𝒜', f, h⟩ := h𝒜.exists_strictUnit_isIso he
  exact ⟨e, 𝒜', f, h⟩

/-- **Keller's unit strictification theorem.**  Let `𝒜` be an `A∞` algebra over a field `K` and let
`e` be a cohomological unit of `𝒜`.  Then the cohomology `𝒜.Cohomology` carries a minimal `A∞`
structure `ℋ` with the cohomology grading and the induced cohomology product, for which the class
`𝒜.cohomologyClass he.cycle` is a strict unit, together with `A∞` quasi-isomorphisms
`i : ℋ ⟶ 𝒜` and `p : 𝒜 ⟶ ℋ` satisfying `p.comp i = id` and `p.linearPart e = [e]`. -/
theorem CohomologicalUnit.exists_strictUnit_minimalModel {𝒜 : AInfinityAlgebra K A} {e : A}
    (he : 𝒜.CohomologicalUnit e) :
    ∃ (ℋ : AInfinityAlgebra K 𝒜.Cohomology) (i : AInfinityHom ℋ 𝒜) (p : AInfinityHom 𝒜 ℋ),
      ℋ.grading = 𝒜.cohomologyGrading ∧ ℋ.IsMinimal ∧
      (∀ x y : 𝒜.Cohomology, ℋ.m 2 ![x, y] = x * y) ∧
      ℋ.StrictUnit (𝒜.cohomologyClass he.cycle) ∧
      i.IsQuasiIso ∧ p.IsQuasiIso ∧
      p.comp i = AInfinityHom.id ℋ ∧
      p.linearPart e = 𝒜.cohomologyClass he.cycle := by
  have hp_e : 𝒜.minimalModelProjection.linearPart e = 𝒜.cohomologyClass he.cycle := by
    rw [linearPart_minimalModelProjection, cohomologyContraction_proj_of_mem_cycles _ he.cycle]
  have he_min : 𝒜.minimalModel.CohomologicalUnit (𝒜.cohomologyClass he.cycle) :=
    hp_e ▸ 𝒜.isQuasiIso_minimalModelProjection.cohomologicalUnit he
  obtain ⟨ℋ, g, hG, hmin, hm2, hstr, hg_iso, hg_lin⟩ :=
    𝒜.isMinimal_minimalModel.exists_strictUnit_isIso he_min
  have hg_bij : Function.Bijective g.linearPart := hg_iso.linearPart_bijective
  let g_inv : AInfinityHom 𝒜.minimalModel ℋ := g.inverse hg_bij
  have hg_inv_lin : g_inv.linearPart = LinearMap.id := LinearMap.ext fun c ↦ by
    have h :=
      LinearMap.congr_fun (congrArg AInfinityHom.linearPart (g.inverse_comp_cancel hg_bij)) c
    simpa only [AInfinityHom.linearPart_comp, hg_lin, LinearMap.comp_id,
      AInfinityHom.linearPart_id, LinearMap.id_apply] using h
  refine ⟨ℋ, 𝒜.minimalModelInclusion.comp g, g_inv.comp 𝒜.minimalModelProjection,
    hG.trans 𝒜.minimalModel_grading, hmin,
    fun x y ↦ by rw [hm2, minimalModel_m_two], hstr,
    𝒜.isQuasiIso_minimalModelInclusion.comp hg_iso.isQuasiIso,
    (g.isIso_inverse hg_bij).isQuasiIso.comp 𝒜.isQuasiIso_minimalModelProjection, ?_, ?_⟩
  · rw [AInfinityHom.comp_assoc, ← AInfinityHom.comp_assoc 𝒜.minimalModelProjection,
      𝒜.minimalModelProjection_comp_minimalModelInclusion, AInfinityHom.id_comp,
      g.inverse_comp_cancel hg_bij]
  · rw [AInfinityHom.linearPart_comp, hg_inv_lin, LinearMap.id_comp, hp_e]

/-- Every cohomologically unital `A∞` algebra over a field admits a strictly unital minimal model
on its cohomology, equipped with section-retraction `A∞` quasi-isomorphisms. -/
theorem CohomologicallyUnital.exists_strictUnit_minimalModel {𝒜 : AInfinityAlgebra K A}
    (hu : 𝒜.CohomologicallyUnital) :
    ∃ (u : 𝒜.Cohomology) (ℋ : AInfinityAlgebra K 𝒜.Cohomology)
      (i : AInfinityHom ℋ 𝒜) (p : AInfinityHom 𝒜 ℋ),
      ℋ.grading = 𝒜.cohomologyGrading ∧ ℋ.IsMinimal ∧
      (∀ x y : 𝒜.Cohomology, ℋ.m 2 ![x, y] = x * y) ∧
      ℋ.StrictUnit u ∧ i.IsQuasiIso ∧ p.IsQuasiIso ∧ p.comp i = AInfinityHom.id ℋ := by
  obtain ⟨e, he⟩ := (cohomologicallyUnital_def 𝒜).1 hu
  obtain ⟨ℋ, i, p, hG, hmin, hm2, hstr, hi, hp, hpi, _⟩ := he.exists_strictUnit_minimalModel
  exact ⟨𝒜.cohomologyClass he.cycle, ℋ, i, p, hG, hmin, hm2, hstr, hi, hp, hpi⟩

/-- Over a field, an `A∞` algebra is cohomologically unital if and only if it receives an `A∞`
quasi-isomorphism from a strictly unital `A∞` algebra (in the same carrier universe). -/
theorem cohomologicallyUnital_iff_exists_strictUnit_isQuasiIso (𝒜 : AInfinityAlgebra K A) :
    𝒜.CohomologicallyUnital ↔
      ∃ (B : Type uA) (_ : AddCommGroup B) (_ : Module K B) (ℬ : AInfinityAlgebra K B)
        (e : B) (f : AInfinityHom ℬ 𝒜), ℬ.StrictUnit e ∧ f.IsQuasiIso := by
  refine ⟨fun hu ↦ ?_, fun ⟨_, _, _, _, _, f, he, hf⟩ ↦
    hf.cohomologicallyUnital_iff.mp he.cohomologicallyUnital⟩
  obtain ⟨u, ℋ, i, _, _, _, _, hstr, hi, _, _⟩ := hu.exists_strictUnit_minimalModel
  exact ⟨𝒜.Cohomology, inferInstance, inferInstance, ℋ, u, i, hstr, hi⟩

/-- Over a field, an `A∞` algebra is cohomologically unital if and only if it admits an `A∞`
quasi-isomorphism to a strictly unital `A∞` algebra (in the same carrier universe). -/
theorem cohomologicallyUnital_iff_exists_strictUnit_isQuasiIso_from (𝒜 : AInfinityAlgebra K A) :
    𝒜.CohomologicallyUnital ↔
      ∃ (B : Type uA) (_ : AddCommGroup B) (_ : Module K B) (ℬ : AInfinityAlgebra K B)
        (e : B) (g : AInfinityHom 𝒜 ℬ), ℬ.StrictUnit e ∧ g.IsQuasiIso := by
  refine ⟨fun hu ↦ ?_, fun ⟨_, _, _, _, _, g, he, hg⟩ ↦
    hg.cohomologicallyUnital_iff.mpr he.cohomologicallyUnital⟩
  obtain ⟨u, ℋ, _, p, _, _, _, hstr, _, hp, _⟩ := hu.exists_strictUnit_minimalModel
  exact ⟨𝒜.Cohomology, inferInstance, inferInstance, ℋ, u, p, hstr, hp⟩

end Field

end TauCeti.AInfinityAlgebra
