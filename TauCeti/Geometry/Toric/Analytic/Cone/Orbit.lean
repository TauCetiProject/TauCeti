/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyClosed
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold

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
`F`.  This is the coordinate-free description of the torus orbit attached to `F`. -/
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
    have hm' : (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ ≠ 0 ↔
        ρ ∉ hσ.faceOrderIso hi F := by
      exact hmcoord
    simpa using not_congr hm'
  · intro hx m
    rw [hσ.realCharacter_eq_zero_on_face_iff hi hb F m]
    let z := coneChartEquiv hi hσ.toIsToricCone hb x
    have heval := coneChartEquiv_symm_apply_single hi hσ.toIsToricCone hb z m
    rw [Equiv.symm_apply_apply] at heval
    constructor
    · intro he ρ hρ
      have hprod : (regularDualSemigroupEquiv hi hσ.toIsToricCone hb m).1.prod
          (fun ρ n ↦ z.1 ρ ^ n) ≠ 0 := (mul_ne_zero_iff.mp (heval ▸ he)).1
      rw [Finsupp.prod_ne_zero_iff] at hprod
      by_contra hn
      have hsupp : ρ ∈ (regularDualSemigroupEquiv hi hσ.toIsToricCone hb m).1.support :=
        Finsupp.mem_support_iff.mpr hn
      have hz : z.1 ρ = 0 := by simpa [z] using (hx ρ).mpr hρ
      exact hprod ρ hsupp (by simp [hz, hn])
    · intro hm
      rw [heval]
      refine mul_ne_zero ?_ (Units.ne_zero _)
      rw [Finsupp.prod_ne_zero_iff]
      intro ρ hρ
      apply pow_ne_zero
      intro hz
      exact Finsupp.mem_support_iff.mp hρ (hm ρ ((hx ρ).mp (by simpa [z] using hz)))

/-! ### Coordinate strata -/

/-- The coordinate stratum attached to a set of rays: precisely those mixed coordinates whose
ray coordinates vanish on that set and nowhere else.  The complementary coordinates are
unrestricted units. -/
def coneOrbitCoordinateSet (A : Set (ToricRay σ)) :
    Set ((ToricRay σ → ℂ) × (ι → ℂˣ)) :=
  {z | ∀ ρ, z.1 ρ = 0 ↔ ρ ∈ A}

/-- A mixed coordinate point belongs to the stratum attached to `A` exactly when its ray
coordinate vanishes precisely on `A`. -/
@[simp]
theorem mem_coneOrbitCoordinateSet (A : Set (ToricRay σ))
    (z : (ToricRay σ → ℂ) × (ι → ℂˣ)) :
    z ∈ coneOrbitCoordinateSet (ι := ι) A ↔ ∀ ρ, z.1 ρ = 0 ↔ ρ ∈ A :=
  Iff.rfl

/-- Under any extending-basis chart, the intrinsic orbit of `F` is the inverse image of the
coordinate stratum attached to the rays of `F`. -/
theorem preimage_coneOrbitCoordinateSet_eq_affineConeOrbit (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face) :
    coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
        coneOrbitCoordinateSet (ι := ι) (hσ.faceOrderIso hi F) =
      affineConeOrbit hi F := by
  ext x
  rw [Set.mem_preimage, mem_coneOrbitCoordinateSet,
    mem_affineConeOrbit_iff_coneChartEquiv]

/-- The coordinate stratum attached to a set of rays is locally closed. -/
theorem isLocallyClosed_coneOrbitCoordinateSet (A : Set (ToricRay σ))
    [Finite (ToricRay σ)] :
    IsLocallyClosed (coneOrbitCoordinateSet (ι := ι) A) := by
  classical
  let U : Set ((ToricRay σ → ℂ) × (ι → ℂˣ)) :=
    {z | ∀ ρ, ρ ∉ A → z.1 ρ ≠ 0}
  let Z : Set ((ToricRay σ → ℂ) × (ι → ℂˣ)) :=
    {z | ∀ ρ, ρ ∈ A → z.1 ρ = 0}
  have hcontinuous : ∀ ρ : ToricRay σ,
      Continuous (fun z : (ToricRay σ → ℂ) × (ι → ℂˣ) ↦ z.1 ρ) :=
    fun ρ ↦ (continuous_apply ρ).comp continuous_fst
  have hU : IsOpen U := by
    have hUeq : U = ⋂ ρ, ⋂ (_ : ρ ∉ A),
        (fun z : (ToricRay σ → ℂ) × (ι → ℂˣ) ↦ z.1 ρ) ⁻¹' ({0}ᶜ) := by
      ext z
      simp [U]
    rw [hUeq]
    exact isOpen_iInter_of_finite fun ρ ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_compl_singleton.preimage (hcontinuous ρ)
  have hZ : IsClosed Z := by
    have hZeq : Z = ⋂ ρ, ⋂ (_ : ρ ∈ A),
        (fun z : (ToricRay σ → ℂ) × (ι → ℂˣ) ↦ z.1 ρ) ⁻¹' ({0}) := by
      ext z
      simp [Z]
    rw [hZeq]
    exact isClosed_iInter fun ρ ↦ isClosed_iInter fun _ ↦
      isClosed_singleton.preimage (hcontinuous ρ)
  refine ⟨U, Z, hU, hZ, ?_⟩
  ext z
  simp only [mem_coneOrbitCoordinateSet, Set.mem_inter_iff]
  constructor
  · intro hz
    exact ⟨fun ρ hρ ↦ (hz ρ).not.mpr hρ, fun ρ hρ ↦ (hz ρ).mpr hρ⟩
  · rintro ⟨hU', hZ'⟩ ρ
    exact ⟨fun h ↦ Classical.byContradiction fun hn ↦ hU' ρ hn h,
      fun h ↦ hZ' ρ h⟩

/-- The closure of a coordinate stratum permits additional ray coordinates to vanish, while
retaining the coordinates already forced to be zero. -/
theorem closure_coneOrbitCoordinateSet (A : Set (ToricRay σ)) :
    closure (coneOrbitCoordinateSet (ι := ι) A) =
      {z | ∀ ρ ∈ A, z.1 ρ = 0} := by
  classical
  have hset : coneOrbitCoordinateSet (ι := ι) A =
      (Set.pi Set.univ fun ρ ↦ if ρ ∈ A then {0} else {0}ᶜ) ×ˢ Set.univ := by
    ext z
    rw [mem_coneOrbitCoordinateSet]
    simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, and_true]
    exact forall_congr' fun ρ ↦ by by_cases hρ : ρ ∈ A <;> simp [hρ]
  rw [hset, closure_prod_eq, closure_pi_set]
  ext z
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, closure_univ, and_true]
  constructor
  · intro hz ρ hρ
    simpa [hρ] using hz ρ
  · intro hz ρ
    by_cases hρ : ρ ∈ A
    · simpa [hρ] using hz ρ hρ
    · simp [hρ]

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
theorem exists_unique_face_mem_affineConeOrbit (hi : IsIntegralLattice i)
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
  exact (isLocallyClosed_coneOrbitCoordinateSet (A := hσ.faceOrderIso hi F)).preimage
    (by simpa only [coe_coneChartHomeomorph hi hσ.toIsToricCone hb g] using
      (coneChartHomeomorph hi hσ.toIsToricCone hb g).continuous)

/-- The closure of the orbit of `F` consists of the points whose coordinates at all rays of `F`
vanish; coordinates at other rays may vanish as well. -/
theorem closure_affineConeOrbit (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
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
    (coneOrbitCoordinateSet (ι := ι) (hσ.faceOrderIso hi F))
  rw [coe_coneChartHomeomorph] at hpre
  calc
    closure (affineConeOrbit hi F) = closure
        (coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
          coneOrbitCoordinateSet (hσ.faceOrderIso hi F)) :=
      congrArg closure (preimage_coneOrbitCoordinateSet_eq_affineConeOrbit hi hσ hb F).symm
    _ = coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
        closure (coneOrbitCoordinateSet (hσ.faceOrderIso hi F)) := hpre.symm
    _ = {x | ∀ ρ ∈ hσ.faceOrderIso hi F,
        (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0} := by
      rw [closure_coneOrbitCoordinateSet]
      rfl

/-- Face inclusion is the reverse closure order on affine-cone orbits. -/
theorem affineConeOrbit_subset_closure_iff (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (F G : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    affineConeOrbit hi G ⊆ closure (affineConeOrbit hi F) ↔ F ≤ G := by
  dsimp only
  let _ := affinePointTopology g
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  rw [closure_affineConeOrbit hi hσ hb F g]
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
