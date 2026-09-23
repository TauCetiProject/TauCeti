/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyClosed
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face
public import TauCeti.Geometry.Toric.Analytic.Cone.Chart

/-!
# Orbit strata of a regular affine toric cone

The face `F` of a regular toric cone determines a stratum of its affine complex points.  A point
belongs to this stratum precisely when a monomial is nonzero at the point exactly when its
character vanishes on `F`.  This description is intrinsic: it uses neither an extending basis nor
a numbering of the rays.

In regular coordinates, the stratum has the familiar form: the coordinate indexed by a ray is
zero exactly when that ray belongs to `F`; every complementary coordinate is already invertible.
This identifies the strata with the coordinate pieces of the mixed chart.  In particular, every
stratum is nonempty and locally closed, the strata are pairwise disjoint and cover the affine
chart, and their closure order is the reverse of the face order.

## Main declarations

* `TauCeti.Toric.affineConeOrbit`: the intrinsic stratum associated to a face.
* `TauCeti.Toric.mem_affineConeOrbit_iff_coneChartEquiv`: its coordinate zero-pattern.
* `TauCeti.Toric.isLocallyClosed_affineConeOrbit`: every affine-cone orbit is locally closed.
* `TauCeti.Toric.closure_affineConeOrbit`: the intrinsic union formula for its closure.
* `TauCeti.Toric.affineConeOrbit_subset_closure_iff`: face inclusion is the reverse closure order.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1–2.2.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2.
-/

public section

open Multiplicative Set Topology

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V} {s : ℕ}

/-- The stratum of the affine toric chart associated to a face `F`.  Its points are those for
which a monomial is nonzero exactly when the corresponding character vanishes identically on
`F`.  This is the coordinate-free description of the stratum attached to `F`; its identification
as an orbit of the dense torus is not established here. -/
def affineConeOrbit (hi : IsIntegralLattice i) (F : σ.Face) :
    Set (AffineSemigroupComplexPoint (dualSemigroup hi σ)) :=
  {x | ∀ m : dualSemigroup hi σ,
    x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 ↔
      ∀ y, y ∈ F → hi.realCharacter (m : N →+ ℤ) y = 0}

/-- Membership in an affine-cone orbit is characterized by nonvanishing of precisely the
monomials whose characters vanish on the associated face. -/
theorem mem_affineConeOrbit (hi : IsIntegralLattice i) (F : σ.Face)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    x ∈ affineConeOrbit hi F ↔ ∀ m : dualSemigroup hi σ,
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 ↔
        ∀ y, y ∈ F → hi.realCharacter (m : N →+ ℤ) y = 0 :=
  Iff.rfl

/-- In regular coordinates, a point belongs to the orbit of `F` exactly when its ray coordinate
is zero precisely at the rays contained in `F`. -/
theorem mem_affineConeOrbit_iff_coneChartEquiv (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    x ∈ affineConeOrbit hi F ↔
      ∀ ρ, (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0 ↔
        ρ ∈ hσ.faceOrderIso hi F := by
  classical
  rw [mem_affineConeOrbit]
  constructor
  · intro hx ρ
    let m := dualSemigroupCoord hi hσ.toIsToricCone hb (Sum.inl ρ)
    have hm := hx m
    rw [← coneChartEquiv_fst_apply hi hσ.toIsToricCone hb x ρ] at hm
    have hmcoord := hm.trans (hσ.realCharacter_eq_zero_on_face_iff hi hb F m)
    rw [regularDualSemigroupEquiv_fst_dualSemigroupCoord_inl
      hi hσ.toIsToricCone hb hb] at hmcoord
    have hrhs : (∀ ρ' ∈ hσ.faceOrderIso hi F, (Finsupp.single ρ 1) ρ' = 0) ↔
        ρ ∉ hσ.faceOrderIso hi F := by
      constructor
      · intro h hρ
        simpa using h ρ hρ
      · intro h ρ' hρ'
        rw [Finsupp.single_apply]
        split <;> simp_all
    rw [hrhs] at hmcoord
    simpa using not_congr hmcoord
  · intro hx m
    rw [hσ.realCharacter_eq_zero_on_face_iff hi hb F m,
      coneChartEquiv_apply_single_ne_zero_iff hi hσ.toIsToricCone hb x m]
    constructor
    · intro hz ρ hρ
      by_contra hm
      exact hz ρ (Finsupp.mem_support_iff.mpr hm) ((hx ρ).mpr hρ)
    · intro hm ρ hρ hz
      exact Finsupp.mem_support_iff.mp hρ (hm ρ ((hx ρ).mp hz))

/-! ### Coordinate strata -/

/-- The coordinate stratum attached to a subset `A` of an index type: precisely those pairs whose
first coordinates vanish on `A` and nowhere else.  The second component is unrestricted. -/
def coneOrbitCoordinateSet (α β : Type*) (A : Set α) : Set ((α → ℂ) × β) :=
  {z | ∀ a, z.1 a = 0 ↔ a ∈ A}

/-- A coordinate pair belongs to the stratum attached to `A` exactly when its first coordinate
vanishes precisely on `A`. -/
@[simp]
theorem mem_coneOrbitCoordinateSet (α β : Type*) (A : Set α) (z : (α → ℂ) × β) :
    z ∈ coneOrbitCoordinateSet α β A ↔ ∀ a, z.1 a = 0 ↔ a ∈ A :=
  Iff.rfl

/-- The coordinate stratum is a product of single-coordinate conditions with an unrestricted
second factor. -/
theorem coneOrbitCoordinateSet_eq_pi_prod (α β : Type*) (A : Set α) :
    coneOrbitCoordinateSet α β A =
      (Set.pi Set.univ fun a ↦ {z : ℂ | z = 0 ↔ a ∈ A}) ×ˢ Set.univ := by
  ext z
  rw [mem_coneOrbitCoordinateSet]
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, and_true]
  rfl

/-- Under any extending-basis chart, the intrinsic orbit of `F` is the inverse image of the
coordinate stratum attached to the rays of `F`. -/
theorem preimage_coneOrbitCoordinateSet_eq_affineConeOrbit (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face) :
    coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
        coneOrbitCoordinateSet (ToricRay σ) (ι → ℂˣ) (hσ.faceOrderIso hi F) =
      affineConeOrbit hi F := by
  ext x
  rw [Set.mem_preimage, mem_coneOrbitCoordinateSet,
    mem_affineConeOrbit_iff_coneChartEquiv]

/-- A coordinate stratum with finitely many first coordinates is locally closed. -/
theorem isLocallyClosed_coneOrbitCoordinateSet (α β : Type*) [Finite α]
    [TopologicalSpace β] (A : Set α) : IsLocallyClosed (coneOrbitCoordinateSet α β A) := by
  classical
  let U := (Set.pi Aᶜ fun _ ↦ ({0}ᶜ : Set ℂ)) ×ˢ (Set.univ : Set β)
  let Z := (Set.pi A fun _ ↦ ({0} : Set ℂ)) ×ˢ (Set.univ : Set β)
  have hU : IsOpen U :=
    (isOpen_set_pi (Set.toFinite _) fun _ _ ↦ isOpen_compl_singleton).prod isOpen_univ
  have hZ : IsClosed Z :=
    (isClosed_set_pi fun _ _ ↦ isClosed_singleton).prod isClosed_univ
  refine ⟨U, Z, hU, hZ, ?_⟩
  ext z
  simp only [mem_coneOrbitCoordinateSet, Set.mem_inter_iff, U, Z, Set.mem_prod, Set.mem_pi,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, and_true]
  constructor
  · intro hz
    exact ⟨fun a ha ↦ (hz a).not.mpr ha, fun a ha ↦ (hz a).mpr ha⟩
  · rintro ⟨hU', hZ'⟩ a
    exact ⟨fun h ↦ Classical.byContradiction fun hn ↦ hU' a hn h,
      fun h ↦ hZ' a h⟩

/-- The closure of a coordinate stratum permits additional first coordinates to vanish, while
retaining the coordinates already forced to be zero. -/
theorem closure_coneOrbitCoordinateSet (α β : Type*) [TopologicalSpace β] (A : Set α) :
    closure (coneOrbitCoordinateSet α β A) = {z | ∀ a ∈ A, z.1 a = 0} := by
  classical
  rw [coneOrbitCoordinateSet_eq_pi_prod, closure_prod_eq, closure_pi_set]
  ext z
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, closure_univ, and_true]
  constructor
  · intro hz ρ hρ
    simpa [hρ] using hz ρ
  · intro hz ρ
    by_cases hρ : ρ ∈ A
    · simpa [hρ] using hz ρ hρ
    · have hne : {w : ℂ | ¬w = 0} = ({0}ᶜ : Set ℂ) := by ext w; simp
      simp only [hρ, iff_false, hne]
      rw [closure_compl_singleton]
      exact Set.mem_univ _

/-! ### Intrinsic consequences -/

private theorem affineConeOrbit_nonempty_of_basis (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ)
    {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face) :
    (affineConeOrbit hi F).Nonempty := by
  classical
  refine ⟨(coneChartEquiv hi hσ.toIsToricCone hb).symm
    (fun ρ ↦ if ρ ∈ hσ.faceOrderIso hi F then 0 else 1, fun _ ↦ 1), ?_⟩
  apply (mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb F _).2
  rw [Equiv.apply_symm_apply]
  intro ρ
  by_cases hρ : ρ ∈ hσ.faceOrderIso hi F <;> simp

/-- Every face-indexed affine-cone orbit is nonempty. -/
theorem affineConeOrbit_nonempty (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) : (affineConeOrbit hi F).Nonempty := by
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  exact affineConeOrbit_nonempty_of_basis hi hσ hb F

/-- The orbit strata form a partition: every affine complex point belongs to the orbit of a
unique face. -/
theorem existsUnique_face_mem_affineConeOrbit (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    ∃! F : σ.Face, x ∈ affineConeOrbit hi F := by
  classical
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  let A : Set (ToricRay σ) := {ρ | (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0}
  refine ⟨(hσ.faceOrderIso hi).symm A, ?_, ?_⟩
  · apply (mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb _ x).2
    rw [OrderIso.apply_symm_apply]
    intro ρ
    rfl
  · intro F hF
    apply (hσ.faceOrderIso hi).injective
    ext ρ
    rw [OrderIso.apply_symm_apply]
    exact ((mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb F x).mp hF ρ).symm

/-- Every affine-cone orbit is locally closed in the monomial-embedding topology. -/
theorem isLocallyClosed_affineConeOrbit (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    IsLocallyClosed (affineConeOrbit hi F) := by
  let _ := affinePointTopology g
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  let _ := ToricRay.finite_of_fg hσ.fg
  rw [← preimage_coneOrbitCoordinateSet_eq_affineConeOrbit hi hσ hb F]
  exact (isLocallyClosed_coneOrbitCoordinateSet (ToricRay σ) (Fin l → ℂˣ)
    (hσ.faceOrderIso hi F)).preimage
    (by simpa only [coe_coneChartHomeomorph hi hσ.toIsToricCone hb g] using
      (coneChartHomeomorph hi hσ.toIsToricCone hb g).continuous)

/-- The closure of the orbit of `F` consists of the points whose coordinates at all rays of `F`
vanish; coordinates at other rays may vanish as well. -/
private theorem closure_affineConeOrbit_eq_coordinate (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ)
    {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    closure (affineConeOrbit hi F) =
      {x | ∀ ρ ∈ hσ.faceOrderIso hi F,
        (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0} := by
  dsimp only
  let _ := affinePointTopology g
  have hpre := (coneChartHomeomorph hi hσ.toIsToricCone hb g).preimage_closure
    (coneOrbitCoordinateSet (ToricRay σ) (ι → ℂˣ) (hσ.faceOrderIso hi F))
  rw [coe_coneChartHomeomorph] at hpre
  calc
    closure (affineConeOrbit hi F) = closure
        (coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
          coneOrbitCoordinateSet (ToricRay σ) (ι → ℂˣ) (hσ.faceOrderIso hi F)) :=
      congrArg closure (preimage_coneOrbitCoordinateSet_eq_affineConeOrbit hi hσ hb F).symm
    _ = coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
        closure (coneOrbitCoordinateSet (ToricRay σ) (ι → ℂˣ)
          (hσ.faceOrderIso hi F)) := hpre.symm
    _ = {x | ∀ ρ ∈ hσ.faceOrderIso hi F,
        (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0} := by
      rw [closure_coneOrbitCoordinateSet]
      rfl

/-- The closure of the orbit stratum of `F` is the union of the strata indexed by faces
containing `F`. -/
theorem closure_affineConeOrbit (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    closure (affineConeOrbit hi F) = ⋃ G ∈ Set.Ici F, affineConeOrbit hi G := by
  dsimp only
  let _ := affinePointTopology g
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  rw [closure_affineConeOrbit_eq_coordinate hi hσ hb F g]
  ext x
  constructor
  · intro hx
    obtain ⟨G, hxG, -⟩ := existsUnique_face_mem_affineConeOrbit hi hσ x
    have hFG : F ≤ G := by
      apply (hσ.faceOrderIso hi).le_iff_le.mp
      intro ρ hρ
      exact ((mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb G x).mp hxG ρ).mp
        (hx ρ hρ)
    exact Set.mem_iUnion.2 ⟨G, Set.mem_iUnion.2 ⟨hFG, hxG⟩⟩
  · intro hx
    obtain ⟨G, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hFG, hxG⟩ := Set.mem_iUnion.1 hx
    intro ρ hρ
    exact ((mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb G x).mp hxG ρ).mpr
      ((hσ.faceOrderIso hi).monotone hFG hρ)

/-- Face inclusion is the reverse closure order on affine-cone orbits. -/
theorem affineConeOrbit_subset_closure_iff (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (F G : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    affineConeOrbit hi G ⊆ closure (affineConeOrbit hi F) ↔ F ≤ G := by
  dsimp only
  let _ := affinePointTopology g
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  rw [closure_affineConeOrbit_eq_coordinate hi hσ hb F g]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := affineConeOrbit_nonempty hi hσ G
    apply (hσ.faceOrderIso hi).le_iff_le.mp
    intro ρ hρ
    have hcoord := (mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb G x).mp hx
    exact (hcoord ρ).mp (h hx ρ hρ)
  · intro h x hx ρ hρ
    have hcoord := (mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb G x).mp hx
    exact (hcoord ρ).mpr ((hσ.faceOrderIso hi).monotone h hρ)

end TauCeti.Toric
