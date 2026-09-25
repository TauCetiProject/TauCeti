/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Continuity of homomorphisms and maps involving subgroups and quotients

Mathlib's `Subgroup.subtype` and `QuotientGroup.mk'` are bare `MonoidHom`s, and its coercion
`ContinuousMonoidHom.toContinuousMonoidHom` applies only to bundled types that already carry a
`ContinuousMapClass` instance, so neither map is available as a `ContinuousMonoidHom`. This file
packages those maps for a topological group and the subspace and quotient topologies. It also
provides inverse conjugation `n ↦ g⁻¹ * n * g` on a normal subgroup, together with its evaluation,
identity, and composition laws, and the continuous lift through a quotient by a normal subgroup.
A homomorphism from a topological group with open kernel is also continuous, for every topology
on the target. It also records the pointwise characterization of finite-order continuous
homomorphisms.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous homomorphism into a commutative topological group has finite order exactly when
all its values have a common positive exponent equal to one. -/
theorem _root_.ContinuousMonoidHom.isOfFinOrder_iff_exists_pow_apply_eq_one
    {A B : Type*} [Monoid A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] (f : A →ₜ* B) :
    IsOfFinOrder f ↔ ∃ n, 0 < n ∧ ∀ x, f x ^ n = 1 := by
  constructor
  · rintro h
    obtain ⟨n, hn, hfn⟩ := h.exists_pow_eq_one
    refine ⟨n, hn, fun x ↦ ?_⟩
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply]
      using DFunLike.congr_fun hfn x
  · rintro ⟨n, hn, h⟩
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using h x

/-- A homomorphism with open kernel out of a topological group is continuous for every topology
on the target: it is constant on the open coset `x * ker f` of each point `x`. -/
theorem _root_.MonoidHom.continuous_of_isOpen_ker [ContinuousMul G] {F : Type*} [MulOneClass F]
    [TopologicalSpace F] (f : G →* F) (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x ↦ tendsto_const_nhds.congr' ?_
  have hcoset : ∀ᶠ y in nhds x, x⁻¹ * y ∈ f.ker := by
    have hmul : Filter.Tendsto (fun y ↦ x⁻¹ * y) (nhds x) (nhds 1) := by
      simpa using (continuous_const_mul x⁻¹).tendsto x
    exact hmul.eventually (Filter.eventually_mem_set.mpr (hf.mem_nhds (one_mem f.ker)))
  filter_upwards [hcoset] with y hy
  calc f x = f x * f (x⁻¹ * y) := by rw [MonoidHom.mem_ker.mp hy, mul_one]
    _ = f y := by rw [← map_mul, mul_inv_cancel_left]

namespace ContinuousMonoidHom

/-- Evaluating a continuous homomorphism assembled from a homomorphism and a continuity proof. -/
@[simp]
theorem _root_.ContinuousMonoidHom.coe_mk {A B : Type*} [Monoid A] [TopologicalSpace A] [Monoid B]
    [TopologicalSpace B] (f : A →* B) (hf : Continuous f) : ⇑(⟨f, hf⟩ : A →ₜ* B) = f :=
  rfl

-- Both definitions below are exposed: downstream, `TopRep.res` objects taken along them have to
-- be definitionally the ones taken along the bare `Subgroup.subtype` and `QuotientGroup.mk'`.
/-- The inclusion of a subgroup, carrying the subspace topology, as a continuous homomorphism. -/
@[expose] def subgroupSubtype (S : Subgroup G) : S →ₜ* G where
  __ := S.subtype
  continuous_toFun := continuous_subtype_val

@[simp]
theorem coe_subgroupSubtype (S : Subgroup G) : (subgroupSubtype S : S →* G) = S.subtype :=
  (rfl)

@[simp]
theorem subgroupSubtype_apply (S : Subgroup G) (s : S) : subgroupSubtype S s = (s : G) :=
  (rfl)

end ContinuousMonoidHom

/-- The inverse conjugation homomorphism of a normal subgroup, with the subspace topology. -/
def _root_.Subgroup.inverseConjugationHom [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (g : G) : N →ₜ* N where
  toMonoidHom := (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom
  continuous_toFun := by
    have hf : Continuous (fun n : N =>
        (⟨g⁻¹ * (n : G) * g, by
          simpa only [inv_inv] using
            (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩ : N)) := by
      -- Conjugation by a fixed element is already a Mathlib continuity theorem.
      exact (((IsTopologicalGroup.continuous_conj (G := G) g⁻¹).comp
        continuous_subtype_val).subtype_mk (fun n => by
          simpa only [Function.comp_apply, inv_inv] using
            (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹)).congr fun n => by
          apply Subtype.ext
          simp
    exact hf.congr fun n => by
      -- The bundled automorphism and the displayed inverse-conjugation formula are definitionally
      -- the same map after taking underlying values.
      apply Subtype.ext
      simp

/-- Evaluation of inverse conjugation on a subgroup element. -/
@[simp]
theorem _root_.Subgroup.inverseConjugationHom_apply [IsTopologicalGroup G] (N : Subgroup G)
    [N.Normal] (g : G) (n : N) :
    _root_.Subgroup.inverseConjugationHom N g n =
      ⟨g⁻¹ * (n : G) * g, by
        simpa only [inv_inv] using
          (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩ := by
  -- `MulAut.conjNormal` is bundled, while the right-hand side exposes its subtype value.
  apply Subtype.ext
  change ((MulAut.conjNormal g⁻¹ : MulAut N) n : G) = _
  simp

/-- Inverse conjugation by the identity is the identity continuous homomorphism. -/
@[simp]
theorem _root_.Subgroup.inverseConjugationHom_one [IsTopologicalGroup G] (N : Subgroup G)
    [N.Normal] :
    _root_.Subgroup.inverseConjugationHom N 1 = ContinuousMonoidHom.id N := by
  ext n
  simp [_root_.Subgroup.inverseConjugationHom_apply]

/-- Inverse conjugation by a product is the reversed composition of inverse conjugations. -/
@[simp]
theorem _root_.Subgroup.inverseConjugationHom_mul [IsTopologicalGroup G] (N : Subgroup G)
    [N.Normal] (g h : G) :
    _root_.Subgroup.inverseConjugationHom N (g * h) =
      (_root_.Subgroup.inverseConjugationHom N h).comp
        (_root_.Subgroup.inverseConjugationHom N g) := by
  ext n
  simp [_root_.Subgroup.inverseConjugationHom_apply, mul_assoc]

namespace ContinuousMonoidHom

/-- The projection onto the quotient by a normal subgroup, carrying the quotient topology, as a
continuous homomorphism. -/
@[expose] def quotientMk (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  __ := QuotientGroup.mk' N
  continuous_toFun := continuous_quot_mk

@[simp]
theorem coe_quotientMk (N : Subgroup G) [N.Normal] :
    (quotientMk N : G →* G ⧸ N) = QuotientGroup.mk' N :=
  (rfl)

@[simp]
theorem quotientMk_apply (N : Subgroup G) [N.Normal] (g : G) : quotientMk N g = (g : G ⧸ N) :=
  (rfl)

/-- The continuous homomorphism induced on a quotient by a continuous homomorphism that kills
the normal subgroup. -/
def quotientLift {H : Type*} [Monoid H] [TopologicalSpace H] (N : Subgroup G)
    [N.Normal] (f : G →ₜ* H) (hf : N ≤ f.ker) : (G ⧸ N) →ₜ* H where
  toMonoidHom := QuotientGroup.lift N f.toMonoidHom hf
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr f.continuous

@[simp]
theorem coe_quotientLift {H : Type*} [Monoid H] [TopologicalSpace H] (N : Subgroup G)
    [N.Normal] (f : G →ₜ* H) (hf : N ≤ f.ker) :
    (quotientLift N f hf : (G ⧸ N) →* H) = QuotientGroup.lift N f.toMonoidHom hf := (rfl)

/-- Evaluation of the quotient lift on a class represented by `x`. -/
@[simp]
theorem quotientLift_mk {H : Type*} [Monoid H] [TopologicalSpace H] (N : Subgroup G)
    [N.Normal] (f : G →ₜ* H) (hf : N ≤ f.ker) (x : G) :
    quotientLift N f hf (x : G ⧸ N) = f x :=
  QuotientGroup.lift_mk' (N := N) (φ := f.toMonoidHom) (HN := hf) x

/-- Composition of the quotient lift with the quotient projection recovers the original map. -/
@[simp]
theorem quotientLift_comp_quotientMk {H : Type*} [Monoid H] [TopologicalSpace H]
    (N : Subgroup G) [N.Normal] (f : G →ₜ* H) (hf : N ≤ f.ker) :
    (quotientLift N f hf).comp (quotientMk N) = f := by
  ext x
  simp

/-- A continuous homomorphism on the quotient is determined by its values on representatives. -/
theorem quotientLift_unique {H : Type*} [Monoid H] [TopologicalSpace H] (N : Subgroup G)
    [N.Normal] (f : G →ₜ* H) (hf : N ≤ f.ker) (g : (G ⧸ N) →ₜ* H)
    (hg : ∀ x : G, g (x : G ⧸ N) = f x) : g = quotientLift N f hf := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  simpa only [QuotientGroup.mk'_apply, quotientLift_mk] using hg x

/-- The kernel of precomposition with the quotient projection contains the subgroup. -/
theorem le_ker_comp_quotientMk {H : Type*} [Monoid H] [TopologicalSpace H]
    (N : Subgroup G) [N.Normal] (g : (G ⧸ N) →ₜ* H) :
    N ≤ ((g.comp (quotientMk N) : G →* H)).ker :=
  fun x hx => by simp [MonoidHom.mem_ker, (QuotientGroup.eq_one_iff x).mpr hx]

/-- Precomposition with the quotient projection identifies continuous homomorphisms on the
quotient with continuous homomorphisms whose kernels contain the normal subgroup. -/
def quotientHomEquiv {H : Type*} [Monoid H] [TopologicalSpace H] (N : Subgroup G)
    [N.Normal] :
    ((G ⧸ N) →ₜ* H) ≃ {f : G →ₜ* H // N ≤ (f : G →* H).ker} where
  toFun g := ⟨g.comp (quotientMk N), le_ker_comp_quotientMk N g⟩
  invFun f := quotientLift N f.val f.property
  left_inv g := (quotientLift_unique N (g.comp (quotientMk N))
    (le_ker_comp_quotientMk N g) g (by intro x; simp)).symm
  right_inv f := by
    apply Subtype.ext
    exact quotientLift_comp_quotientMk N f.val f.property

/-- Evaluation of the forward quotient homomorphism equivalence. -/
@[simp]
theorem quotientHomEquiv_apply_coe {H : Type*} [Monoid H] [TopologicalSpace H]
    (N : Subgroup G) [N.Normal] (g : (G ⧸ N) →ₜ* H) :
    ((quotientHomEquiv N g : {f : G →ₜ* H // N ≤ (f : G →* H).ker}) : G →ₜ* H) =
      g.comp (quotientMk N) := (rfl)

/-- Evaluation of the inverse quotient homomorphism equivalence. -/
@[simp]
theorem quotientHomEquiv_symm_apply {H : Type*} [Monoid H] [TopologicalSpace H]
    (N : Subgroup G) [N.Normal] (f : {f : G →ₜ* H // N ≤ (f : G →* H).ker}) :
    (quotientHomEquiv N).symm f = quotientLift N f.val f.property := (rfl)

end ContinuousMonoidHom

end TauCeti
