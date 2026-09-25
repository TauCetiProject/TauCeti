/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import TauCeti.Topology.ZeroPattern

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
* `TauCeti.Toric.closure_affineConeOrbit_eq_setOf_coneChartEquiv_fst_eq_zero`: the coordinate
  form of its closure.
* `TauCeti.Toric.isLocallyClosed_affineConeOrbit`: every affine-cone orbit is locally closed.
* `TauCeti.Toric.closure_affineConeOrbit`: the intrinsic union formula for its closure.
* `TauCeti.Toric.affineConeOrbit_subset_closure_iff`: face inclusion is the reverse closure order.
* `TauCeti.Toric.affineConeOrbitHomeomorph`: complementary nonzero ray coordinates and torus
  coordinates parametrize an affine orbit with its subspace topology.
* `TauCeti.Toric.isManifold_affineConeOrbitChartedSpace`: these coordinates give the orbit a
  complex-manifold structure.
* `TauCeti.Toric.contMDiff_affineConeOrbitAmbient`: the defining orbit chart is holomorphic.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1–2.2.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2.
-/

public section

open Multiplicative Set Topology
open scoped ContDiff Manifold

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
@[simp]
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
      apply_single_ne_zero_iff_coneChartEquiv_fst_ne_zero hi hσ.toIsToricCone hb x m]
    constructor
    · intro hz ρ hρ
      by_contra hm
      exact hz ρ (Finsupp.mem_support_iff.mpr hm) ((hx ρ).mpr hρ)
    · intro hm ρ hρ hz
      exact Finsupp.mem_support_iff.mp hρ (hm ρ ((hx ρ).mp hz))

/-- Under any extending-basis chart, the intrinsic orbit of `F` is the inverse image of the
coordinate stratum attached to the rays of `F`. -/
theorem preimage_zeroPatternSet_eq_affineConeOrbit (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face) :
    coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
        zeroPatternSet (ToricRay σ) (ι → ℂˣ) ℂ (hσ.faceOrderIso hi F) =
      affineConeOrbit hi F := by
  ext x
  rw [Set.mem_preimage, mem_zeroPatternSet,
    mem_affineConeOrbit_iff_coneChartEquiv]

/-! ### Intrinsic consequences -/

private theorem nonempty_affineConeOrbit_of_basis (hi : IsIntegralLattice i)
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
theorem nonempty_affineConeOrbit (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) : (affineConeOrbit hi F).Nonempty := by
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  exact nonempty_affineConeOrbit_of_basis hi hσ hb F

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
  rw [← preimage_zeroPatternSet_eq_affineConeOrbit hi hσ hb F]
  exact (isLocallyClosed_zeroPatternSet (ToricRay σ) (Fin l → ℂˣ) ℂ
    (hσ.faceOrderIso hi F)).preimage
    (by simpa only [coe_coneChartHomeomorph hi hσ.toIsToricCone hb g] using
      (coneChartHomeomorph hi hσ.toIsToricCone hb g).continuous)

/-- The closure of the orbit of `F` consists of the points whose coordinates at all rays of `F`
vanish; coordinates at other rays may vanish as well. -/
theorem closure_affineConeOrbit_eq_setOf_coneChartEquiv_fst_eq_zero
    (hi : IsIntegralLattice i)
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
    (zeroPatternSet (ToricRay σ) (ι → ℂˣ) ℂ (hσ.faceOrderIso hi F))
  rw [coe_coneChartHomeomorph] at hpre
  calc
    closure (affineConeOrbit hi F) = closure
        (coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
          zeroPatternSet (ToricRay σ) (ι → ℂˣ) ℂ (hσ.faceOrderIso hi F)) :=
      congrArg closure (preimage_zeroPatternSet_eq_affineConeOrbit hi hσ hb F).symm
    _ = coneChartEquiv hi hσ.toIsToricCone hb ⁻¹'
        closure (zeroPatternSet (ToricRay σ) (ι → ℂˣ) ℂ
          (hσ.faceOrderIso hi F)) := hpre.symm
    _ = {x | ∀ ρ ∈ hσ.faceOrderIso hi F,
        (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0} := by
      rw [closure_zeroPatternSet]
      rfl

/-- A point of the orbit of `G` lies in the closure of the orbit of `F` exactly when `F` is a
face of `G`. -/
theorem mem_closure_affineConeOrbit_iff_le (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (F G : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    {x : AffineSemigroupComplexPoint (dualSemigroup hi σ)}
    (hx : x ∈ affineConeOrbit hi G) :
    let _ := affinePointTopology g
    x ∈ closure (affineConeOrbit hi F) ↔ F ≤ G := by
  dsimp only
  let _ := affinePointTopology g
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  rw [closure_affineConeOrbit_eq_setOf_coneChartEquiv_fst_eq_zero hi hσ hb F g]
  constructor
  · intro h
    apply (hσ.faceOrderIso hi).le_iff_le.mp
    intro ρ hρ
    exact ((mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb G x).mp hx ρ).mp
      (h ρ hρ)
  · intro h ρ hρ
    exact ((mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb G x).mp hx ρ).mpr
      ((hσ.faceOrderIso hi).monotone h hρ)

/-- The closure of the orbit stratum of `F` is the union of the strata indexed by faces
containing `F`. -/
theorem closure_affineConeOrbit (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    closure (affineConeOrbit hi F) = ⋃ G ∈ Set.Ici F, affineConeOrbit hi G := by
  dsimp only
  let _ := affinePointTopology g
  ext x
  constructor
  · intro hx
    obtain ⟨G, hxG, -⟩ := existsUnique_face_mem_affineConeOrbit hi hσ x
    have hFG := (mem_closure_affineConeOrbit_iff_le hi hσ F G g hxG).mp hx
    exact Set.mem_iUnion.2 ⟨G, Set.mem_iUnion.2 ⟨hFG, hxG⟩⟩
  · intro hx
    obtain ⟨G, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hFG, hxG⟩ := Set.mem_iUnion.1 hx
    exact (mem_closure_affineConeOrbit_iff_le hi hσ F G g hxG).mpr hFG

/-- Face inclusion is the reverse closure order on affine-cone orbits. -/
theorem affineConeOrbit_subset_closure_iff (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) (F G : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    affineConeOrbit hi G ⊆ closure (affineConeOrbit hi F) ↔ F ≤ G := by
  dsimp only
  let _ := affinePointTopology g
  constructor
  · intro h
    obtain ⟨x, hx⟩ := nonempty_affineConeOrbit hi hσ G
    exact (mem_closure_affineConeOrbit_iff_le hi hσ F G g hx).mp (h hx)
  · intro h x hx
    exact (mem_closure_affineConeOrbit_iff_le hi hσ F G g hx).mpr h

/-- In an extending-basis chart, the orbit of a face is homeomorphic to the nonzero ray
coordinates outside the face, together with all complementary torus coordinates. This gives
the affine orbit its expected product topology without choosing a topology on a new carrier. -/
noncomputable def affineConeOrbitHomeomorph (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    (affineConeOrbit hi F) ≃ₜ
      (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → {z : ℂ // z ≠ 0}) × (ι → ℂˣ)) := by
  let _ := affinePointTopology g
  have hset : affineConeOrbit hi F =
      (coneChartHomeomorph hi hσ.toIsToricCone hb g) ⁻¹'
        zeroPatternSet (ToricRay σ) (ι → ℂˣ) ℂ (hσ.faceOrderIso hi F) := by
    simpa only [coe_coneChartHomeomorph] using
      (preimage_zeroPatternSet_eq_affineConeOrbit hi hσ hb F).symm
  exact ((coneChartHomeomorph hi hσ.toIsToricCone hb g).sets hset).trans
    (zeroPatternSetHomeomorph (ToricRay σ) (ι → ℂˣ) ℂ (hσ.faceOrderIso hi F))

/-- The first orbit coordinates are exactly the nonzero ray coordinates of the affine chart. -/
@[simp]
theorem val_affineConeOrbitHomeomorph_fst_apply (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (x : affineConeOrbit hi F) (ρ : {ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F}) :
    ((affineConeOrbitHomeomorph hi hσ hb F g x).1 ρ).1 =
      (coneChartEquiv hi hσ.toIsToricCone hb x.1).1 ρ.1 := by
  simp [affineConeOrbitHomeomorph, coe_coneChartHomeomorph]

/-- The complementary torus coordinates are unchanged in the orbit chart. -/
@[simp]
theorem affineConeOrbitHomeomorph_snd_apply (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) (x : affineConeOrbit hi F) :
    (affineConeOrbitHomeomorph hi hσ hb F g x).2 =
      (coneChartEquiv hi hσ.toIsToricCone hb x.1).2 := by
  simp [affineConeOrbitHomeomorph, coe_coneChartHomeomorph]

/-- The inverse orbit chart reconstructs the underlying affine point from its coordinates. -/
@[simp]
theorem affineConeOrbitHomeomorph_symm_apply_coe (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (w : ({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → {z : ℂ // z ≠ 0}) ×
      (ι → ℂˣ)) :
    let _ := affinePointTopology g
    (((affineConeOrbitHomeomorph hi hσ hb F g).symm w : affineConeOrbit hi F) :
      AffineSemigroupComplexPoint (dualSemigroup hi σ)) =
      (coneChartEquiv hi hσ.toIsToricCone hb).symm
        ((zeroPatternSetHomeomorph (ToricRay σ) (ι → ℂˣ) ℂ
          (hσ.faceOrderIso hi F)).symm w).1 := by
  let _ := affinePointTopology g
  simp [affineConeOrbitHomeomorph, coe_coneChartHomeomorph_symm]

/-- Ambient coordinates on an affine orbit: retain exactly the nonzero ray coordinates outside
the face, and view all torus coordinates as complex numbers. -/
noncomputable def affineConeOrbitAmbient (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (x : affineConeOrbit hi F) :
    ({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ) :=
  (fun ρ ↦ (coneChartEquiv hi hσ.toIsToricCone hb x.1).1 ρ.1,
    fun j ↦ ((coneChartEquiv hi hσ.toIsToricCone hb x.1).2 j : ℂ))

/-- The first ambient coordinates are the nonzero ray coordinates of the cone chart. -/
@[simp]
theorem affineConeOrbitAmbient_fst_apply (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (x : affineConeOrbit hi F) (ρ : {ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F}) :
    (affineConeOrbitAmbient hi hσ hb F x).1 ρ =
      (coneChartEquiv hi hσ.toIsToricCone hb x.1).1 ρ.1 := by
  simp [affineConeOrbitAmbient]

/-- The second ambient coordinates are the complex values of the torus coordinates. -/
@[simp]
theorem affineConeOrbitAmbient_snd_apply (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (x : affineConeOrbit hi F) (j : ι) :
    (affineConeOrbitAmbient hi hσ hb F x).2 j =
      ((coneChartEquiv hi hσ.toIsToricCone hb x.1).2 j : ℂ) := by
  simp [affineConeOrbitAmbient]

/-- The ambient orbit chart ranges over pairs whose coordinates are all nonzero. -/
theorem range_affineConeOrbitAmbient (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face) :
    Set.range (affineConeOrbitAmbient hi hσ hb F) =
      {w | (∀ ρ, w.1 ρ ≠ 0) ∧ ∀ j, w.2 j ≠ 0} := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun ρ hρ ↦ ρ.2 <|
        ((mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb F x.1).1 x.2 ρ.1).1 hρ,
      fun j ↦ Units.ne_zero _⟩
  · rintro ⟨h₁, h₂⟩
    let z := (zeroPatternSetHomeomorph (ToricRay σ) (ι → ℂˣ) ℂ (hσ.faceOrderIso hi F)).symm
      (fun ρ ↦ ⟨w.1 ρ, h₁ ρ⟩, fun j ↦ Units.mk0 (w.2 j) (h₂ j))
    refine ⟨⟨(coneChartEquiv hi hσ.toIsToricCone hb).symm z.1, ?_⟩, ?_⟩
    · rw [← preimage_zeroPatternSet_eq_affineConeOrbit hi hσ hb F]
      simpa using z.2
    · ext ρ
      · simp [z, zeroPatternSetHomeomorph_symm_fst_apply_of_notMem _ _ _ _ _ _ ρ.2]
      · simp [z]

/-- The retained coordinates realize the affine orbit as an open subset of a complex vector
space. In particular, their topology is the subspace topology inherited from the affine chart. -/
theorem isOpenEmbedding_affineConeOrbitAmbient (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    IsOpenEmbedding (affineConeOrbitAmbient hi hσ hb F) := by
  let _ := affinePointTopology g
  have := hi.finite
  have := Module.Finite.finite_basis b
  have := Finite.sum_left ι (α := ToricRay σ)
  have := Finite.sum_right (ToricRay σ) (β := ι)
  have hcomp : affineConeOrbitAmbient hi hσ hb F =
      Prod.map (Pi.map fun _ ↦ Subtype.val) (Pi.map fun _ ↦ Units.val) ∘
        affineConeOrbitHomeomorph hi hσ hb F g := by
    funext x
    ext <;> simp
  rw [hcomp]
  exact ((IsOpenEmbedding.piMap fun _ ↦
    (isOpen_ne (x := (0 : ℂ))).isOpenEmbedding_subtypeVal).prodMap
      (IsOpenEmbedding.piMap fun _ ↦ Units.isOpenEmbedding_val)).comp
        (affineConeOrbitHomeomorph hi hσ hb F g).isOpenEmbedding

/-- The complex charted-space structure on an affine orbit, using its complementary nonzero ray
coordinates and torus coordinates. The orbit retains the topology induced from the affine chart. -/
@[instance_reducible]
noncomputable def affineConeOrbitChartedSpace (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    let _ := affinePointTopology g
    ChartedSpace
      (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ))
      (affineConeOrbit hi F) := by
  let _ := affinePointTopology g
  let _ : Nonempty (affineConeOrbit hi F) :=
    (nonempty_affineConeOrbit hi hσ F).to_subtype
  exact (isOpenEmbedding_affineConeOrbitAmbient hi hσ hb F g).singletonChartedSpace

/-- Every chart of the orbit charted space is the ambient coordinate map. -/
theorem affineConeOrbitChartedSpace_chartAt (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) (x : affineConeOrbit hi F) :
    let _ := affinePointTopology g
    ⇑(@chartAt (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ))
      _ (affineConeOrbit hi F) _ (affineConeOrbitChartedSpace hi hσ hb F g) x) =
      affineConeOrbitAmbient hi hσ hb F := by
  let _ := affinePointTopology g
  let _ : Nonempty (affineConeOrbit hi F) :=
    (nonempty_affineConeOrbit hi hσ F).to_subtype
  exact (isOpenEmbedding_affineConeOrbitAmbient hi hσ hb F g)
    |>.singletonChartedSpace_chartAt_eq

/-- The target of each orbit chart is the locus of nonzero ambient coordinates. -/
theorem affineConeOrbitChartedSpace_chartAt_target (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) (x : affineConeOrbit hi F) :
    let _ := affinePointTopology g
    (@chartAt (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ))
      _ (affineConeOrbit hi F) _ (affineConeOrbitChartedSpace hi hσ hb F g) x).target =
      {w | (∀ ρ, w.1 ρ ≠ 0) ∧ ∀ j, w.2 j ≠ 0} := by
  let _ := affinePointTopology g
  let _ : Nonempty (affineConeOrbit hi F) :=
    (nonempty_affineConeOrbit hi hσ F).to_subtype
  rw [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq
      ((isOpenEmbedding_affineConeOrbitAmbient hi hσ hb F g).toOpenPartialHomeomorph
        (affineConeOrbitAmbient hi hσ hb F))
      (IsOpenEmbedding.toOpenPartialHomeomorph_source _ _),
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    range_affineConeOrbitAmbient hi hσ hb F]

/-- Every affine-cone orbit is a complex manifold, modeled on the nonzero ray directions outside
its face and the complementary torus directions. -/
theorem isManifold_affineConeOrbitChartedSpace (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    [Fintype {ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F}] [Fintype ι] (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := affineConeOrbitChartedSpace hi hσ hb F g
    IsManifold
      𝓘(ℂ, (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ))) n
      (affineConeOrbit hi F) := by
  let _ := affinePointTopology g
  let _ : Nonempty (affineConeOrbit hi F) :=
    (nonempty_affineConeOrbit hi hσ F).to_subtype
  exact (isOpenEmbedding_affineConeOrbitAmbient hi hσ hb F g).isManifold_singleton

/-- The ambient orbit coordinates are holomorphic for the charted-space structure they induce. -/
theorem contMDiff_affineConeOrbitAmbient (hi : IsIntegralLattice i)
    (hσ : IsRegularCone i σ) {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (F : σ.Face)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    [Fintype {ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F}] [Fintype ι] (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := affineConeOrbitChartedSpace hi hσ hb F g
    ContMDiff 𝓘(ℂ, (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ)))
      𝓘(ℂ, (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ))) n
      (affineConeOrbitAmbient hi hσ hb F) := by
  let _ := affinePointTopology g
  let _ : Nonempty (affineConeOrbit hi F) :=
    (nonempty_affineConeOrbit hi hσ F).to_subtype
  exact contMDiff_isOpenEmbedding (isOpenEmbedding_affineConeOrbitAmbient hi hσ hb F g)

end TauCeti.Toric
