/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face
public import TauCeti.Geometry.Toric.Analytic.Cone.Chart
public import TauCeti.Geometry.Toric.Analytic.Cone.TorusAction
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

The strata are exactly the orbits of the coordinate-free complex torus.  Each stratum contains a
distinguished point, taking the value `1` on the monomials of the characters vanishing on `F` and
`0` on all others; the torus preserves every stratum, and in regular coordinates it moves the
distinguished point to any other point of its stratum by rescaling the nonzero coordinates.  This
is the orbit–cone correspondence for the affine chart: faces of the cone correspond bijectively to
torus orbits, reversing the closure order.  The stabilizer of the distinguished point of `F` is the
subtorus of torus points trivial on the characters vanishing on `F`: those characters are
differences of characters of the dual semigroup vanishing on `F`, because `F` is cut out by a
single character of the dual semigroup.

## Main declarations

* `TauCeti.Toric.affineConeOrbit`: the intrinsic stratum associated to a face.
* `TauCeti.Toric.mem_affineConeOrbit_iff_coneChartEquiv`: its coordinate zero-pattern.
* `TauCeti.Toric.closure_affineConeOrbit_eq_setOf_coneChartEquiv_fst_eq_zero`: the coordinate
  form of its closure.
* `TauCeti.Toric.isLocallyClosed_affineConeOrbit`: every affine-cone orbit is locally closed.
* `TauCeti.Toric.closure_affineConeOrbit`: the intrinsic union formula for its closure.
* `TauCeti.Toric.affineConeOrbit_subset_closure_iff`: face inclusion is the reverse closure order.
* `TauCeti.Toric.distinguishedPoint`: the distinguished point of the stratum of a face, with
  `TauCeti.Toric.distinguishedPoint_apply_single` computing it on monomials and
  `TauCeti.Toric.coneChartEquiv_distinguishedPoint_fst` and
  `TauCeti.Toric.coneChartEquiv_distinguishedPoint_snd` computing its regular coordinates.
* `TauCeti.Toric.smul_mem_affineConeOrbit_iff`: the torus preserves every stratum.
* `TauCeti.Toric.affineConeOrbit_eq_orbit` and `TauCeti.Toric.orbit_eq_affineConeOrbit`: every
  stratum is a single torus orbit.
* `TauCeti.Toric.faceEquivOrbitRelQuotient`: the orbit–cone correspondence between the faces of a
  regular cone and the torus orbits in its affine chart.
* `TauCeti.Toric.mem_stabilizer_distinguishedPoint_iff`: the stabilizer of the distinguished point
  of a face is the subtorus of torus points trivial on the characters vanishing on that face.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1–2.2 and §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and Theorem 3.2.6.
-/

public section

open Multiplicative Set Topology

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V} {s : ℕ}

/-- The stratum of the affine toric chart associated to a face `F`.  Its points are those for
which a monomial is nonzero exactly when the corresponding character vanishes identically on
`F`.  This is the coordinate-free description of the stratum attached to `F`; for a regular cone,
`affineConeOrbit_eq_orbit` identifies it with the torus orbit of `distinguishedPoint hi F`. -/
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

/-! ### The strata are the torus orbits -/

section TorusOrbit

open AffineSemigroupComplexPoint

/-- A character in the dual semigroup of `σ` is nonnegative on every face of `σ`, so the sum of
two such characters vanishes on a face exactly when both summands do. -/
private theorem forall_realCharacter_add_eq_zero_iff (hi : IsIntegralLattice i) (F : σ.Face)
    (m m' : dualSemigroup hi σ) :
    (∀ y, y ∈ F → hi.realCharacter ((m + m' : dualSemigroup hi σ) : N →+ ℤ) y = 0) ↔
      (∀ y, y ∈ F → hi.realCharacter (m : N →+ ℤ) y = 0) ∧
        ∀ y, y ∈ F → hi.realCharacter (m' : N →+ ℤ) y = 0 := by
  have hnonneg (n : dualSemigroup hi σ) (y : V) (hy : y ∈ F) :
      0 ≤ hi.realCharacter (n : N →+ ℤ) y :=
    (mem_dualSemigroup hi _).1 n.2 (F.isFaceOf.le hy)
  simp only [AddSubmonoid.coe_add, map_add, LinearMap.add_apply]
  refine ⟨fun h ↦ ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩, fun h y hy ↦ by rw [h.1 y hy, h.2 y hy, add_zero]⟩
  · exact ((add_eq_zero_iff_of_nonneg (hnonneg m y hy) (hnonneg m' y hy)).1 (h y hy)).1
  · exact ((add_eq_zero_iff_of_nonneg (hnonneg m y hy) (hnonneg m' y hy)).1 (h y hy)).2

open Classical in
/-- The distinguished point of the stratum of a face `F`: the complex point taking the value `1`
on the monomials of the characters that vanish on `F`, and `0` on all other monomials. It lies in
`affineConeOrbit hi F`, and for the smallest face it is the distinguished point `default` of the
dense torus. -/
noncomputable def distinguishedPoint (hi : IsIntegralLattice i) (F : σ.Face) :
    AffineSemigroupComplexPoint (dualSemigroup hi σ) :=
  MonoidAlgebra.lift ℂ ℂ (Multiplicative (dualSemigroup hi σ))
    { toFun m := if ∀ y, y ∈ F → hi.realCharacter ((toAdd m : dualSemigroup hi σ) : N →+ ℤ) y = 0
        then 1 else 0
      map_one' := by simp
      map_mul' m m' := by
        rw [toAdd_mul, forall_realCharacter_add_eq_zero_iff]
        split_ifs <;> simp_all }

open Classical in
/-- The distinguished point of `F` takes the value `1` on the monomial of a character vanishing on
`F`, and `0` on the monomial of any other character. -/
@[simp]
theorem distinguishedPoint_apply_single (hi : IsIntegralLattice i) (F : σ.Face)
    (m : dualSemigroup hi σ) :
    distinguishedPoint hi F (MonoidAlgebra.single (ofAdd m) 1) =
      if ∀ y, y ∈ F → hi.realCharacter (m : N →+ ℤ) y = 0 then 1 else 0 := by
  rw [distinguishedPoint, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd]

/-- The distinguished point of a face lies in the stratum of that face. -/
theorem distinguishedPoint_mem_affineConeOrbit (hi : IsIntegralLattice i) (F : σ.Face) :
    distinguishedPoint hi F ∈ affineConeOrbit hi F := by
  intro m
  rw [distinguishedPoint_apply_single]
  split_ifs with h
  · exact iff_of_true one_ne_zero h
  · exact iff_of_false (not_not.2 rfl) h

/-- Every character of the dual semigroup vanishes on the smallest face of `σ`, its lineality
space, so the distinguished point of that face is the distinguished point `default` of the dense
torus. -/
@[simp]
theorem distinguishedPoint_bot (hi : IsIntegralLattice i) :
    distinguishedPoint hi (⊥ : σ.Face) = default := by
  refine AffineSemigroupComplexPoint.ext fun m ↦ ?_
  have hm (y : V) (hy : y ∈ (⊥ : σ.Face)) : hi.realCharacter (m : N →+ ℤ) y = 0 := by
    rw [← PointedCone.Face.mem_toPointedCone, PointedCone.Face.lineal_eq_bot] at hy
    have h₁ := (mem_dualSemigroup hi _).1 m.2 hy.1
    have h₂ := (mem_dualSemigroup hi _).1 m.2 hy.2
    rw [map_neg] at h₂
    linarith
  rw [distinguishedPoint_apply_single, default_apply_single, ite_eq_left hm]

/-- The torus preserves every stratum: translating a point by a torus point multiplies its value
on each monomial by a unit, so it does not change which monomials vanish. -/
theorem smul_mem_affineConeOrbit_iff (hi : IsIntegralLattice i) (F : σ.Face) (T : ComplexTorus N)
    {x : AffineSemigroupComplexPoint (dualSemigroup hi σ)} :
    T • x ∈ affineConeOrbit hi F ↔ x ∈ affineConeOrbit hi F := by
  simp only [mem_affineConeOrbit, ambient_smul_apply_single, ne_eq, mul_eq_zero, Units.ne_zero,
    false_or]

section Chart

variable (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N} (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

include hσ

open Classical in
/-- In the chart of an extending basis, the ray coordinates of the distinguished point of `F`
vanish at the rays of `F` and equal `1` at all other rays. -/
@[simp]
theorem coneChartEquiv_distinguishedPoint_fst (F : σ.Face) (ρ : ToricRay σ) :
    (coneChartEquiv hi hσ.toIsToricCone hb (distinguishedPoint hi F)).1 ρ =
      if ρ ∈ hσ.faceOrderIso hi F then 0 else 1 := by
  have h := (mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb F _).1
    (distinguishedPoint_mem_affineConeOrbit hi F) ρ
  have h01 : (coneChartEquiv hi hσ.toIsToricCone hb (distinguishedPoint hi F)).1 ρ = 0 ∨
      (coneChartEquiv hi hσ.toIsToricCone hb (distinguishedPoint hi F)).1 ρ = 1 := by
    rw [coneChartEquiv_fst_apply, distinguishedPoint_apply_single]
    split_ifs <;> simp
  split_ifs with hρ
  · exact h.2 hρ
  · exact h01.resolve_left (mt h.1 hρ)

/-- In the chart of an extending basis, the torus coordinates of the distinguished point of every
face are equal to `1`. -/
@[simp]
theorem coneChartEquiv_distinguishedPoint_snd (F : σ.Face) :
    (coneChartEquiv hi hσ.toIsToricCone hb (distinguishedPoint hi F)).2 = 1 := by
  funext j
  refine Units.ext ?_
  have hne := ((coneChartEquiv hi hσ.toIsToricCone hb (distinguishedPoint hi F)).2 j).ne_zero
  rw [val_coneChartEquiv_snd_apply, distinguishedPoint_apply_single] at hne ⊢
  split_ifs at hne ⊢ <;> simp_all

end Chart

/-- The stratum of a face `F` of a regular cone is a single torus orbit, namely the orbit of the
distinguished point of `F`. -/
theorem affineConeOrbit_eq_orbit (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) :
    affineConeOrbit hi F = MulAction.orbit (ComplexTorus N) (distinguishedPoint hi F) := by
  classical
  refine subset_antisymm (fun x hx ↦ ?_) ?_
  · -- In the chart of an extending basis, `x` is obtained from the distinguished point by
    -- multiplying each nonzero coordinate by its value at `x`.
    obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
    let _ := hi.finite
    have hx' := (mem_affineConeOrbit_iff_coneChartEquiv hi hσ hb F x).1 hx
    refine ⟨b.complexTorusCoordinates.symm (Sum.elim
      (fun ρ ↦ if h : (coneChartEquiv hi hσ.toIsToricCone hb x).1 ρ = 0 then 1 else Units.mk0 _ h)
      (coneChartEquiv hi hσ.toIsToricCone hb x).2), ?_⟩
    apply (coneChartEquiv hi hσ.toIsToricCone hb).injective
    refine Prod.ext (funext fun ρ ↦ ?_) (funext fun j ↦ Units.ext ?_)
    · rw [coneChartEquiv_smul_fst, coneChartEquiv_distinguishedPoint_fst hi hσ hb,
        Module.Basis.complexTorusCoordinates_symm_apply, Sum.elim_inl]
      by_cases hρ : ρ ∈ hσ.faceOrderIso hi F
      · rw [ite_eq_left hρ, mul_zero, (hx' ρ).2 hρ]
      · rw [ite_eq_right hρ, mul_one, dite_eq_right (mt (hx' ρ).1 hρ), Units.val_mk0]
    · rw [coneChartEquiv_smul_snd, coneChartEquiv_distinguishedPoint_snd hi hσ hb,
        Module.Basis.complexTorusCoordinates_symm_apply, Sum.elim_inr, Pi.one_apply, mul_one]
  · rintro _ ⟨T, rfl⟩
    exact (smul_mem_affineConeOrbit_iff hi F T).2 (distinguishedPoint_mem_affineConeOrbit hi F)

/-- The torus orbit of any point of the stratum of a face `F` of a regular cone is that whole
stratum. -/
theorem orbit_eq_affineConeOrbit (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    {F : σ.Face} {x : AffineSemigroupComplexPoint (dualSemigroup hi σ)}
    (hx : x ∈ affineConeOrbit hi F) :
    MulAction.orbit (ComplexTorus N) x = affineConeOrbit hi F := by
  rw [affineConeOrbit_eq_orbit hi hσ F] at hx ⊢
  exact (MulAction.orbit_eq_iff (G := ComplexTorus N)).2 hx

/-- The orbit–cone correspondence for the affine chart of a regular cone: the faces of the cone
correspond bijectively to the torus orbits in its complex points, a face `F` corresponding to the
orbit of its distinguished point, which is the stratum `affineConeOrbit hi F`. By
`affineConeOrbit_subset_closure_iff`, the correspondence reverses the closure order. -/
noncomputable def faceEquivOrbitRelQuotient (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    σ.Face ≃ MulAction.orbitRel.Quotient (ComplexTorus N)
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) :=
  Equiv.ofBijective (fun F ↦ Quotient.mk'' (distinguishedPoint hi F)) ⟨fun F G h ↦ by
    have hFG : distinguishedPoint hi F ∈ affineConeOrbit hi G := by
      rw [affineConeOrbit_eq_orbit hi hσ G]
      exact Quotient.exact' h
    exact (existsUnique_face_mem_affineConeOrbit hi hσ _).unique
      (distinguishedPoint_mem_affineConeOrbit hi F) hFG, fun q ↦ by
    induction q using Quotient.inductionOn' with
    | h x =>
      obtain ⟨F, hF, -⟩ := existsUnique_face_mem_affineConeOrbit hi hσ x
      rw [affineConeOrbit_eq_orbit hi hσ F] at hF
      exact ⟨F, Quotient.sound' (MulAction.mem_orbit_symm.1 hF)⟩⟩

/-- The orbit–cone correspondence sends a face to the orbit of its distinguished point. -/
@[simp]
theorem faceEquivOrbitRelQuotient_apply (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) :
    faceEquivOrbitRelQuotient hi hσ F = Quotient.mk'' (distinguishedPoint hi F) :=
  (rfl)

/-- The torus orbit corresponding to a face is its stratum. -/
@[simp]
theorem orbit_faceEquivOrbitRelQuotient (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) :
    (faceEquivOrbitRelQuotient hi hσ F).orbit = affineConeOrbit hi F := by
  rw [faceEquivOrbitRelQuotient_apply, MulAction.orbitRel.Quotient.orbit_mk,
    affineConeOrbit_eq_orbit hi hσ F]

/-- The face corresponding to the torus orbit of a point is the face whose stratum contains it. -/
@[simp]
theorem faceEquivOrbitRelQuotient_symm_mk (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    {F : σ.Face} {x : AffineSemigroupComplexPoint (dualSemigroup hi σ)}
    (hx : x ∈ affineConeOrbit hi F) :
    (faceEquivOrbitRelQuotient hi hσ).symm (Quotient.mk'' x) = F := by
  rw [Equiv.symm_apply_eq, faceEquivOrbitRelQuotient_apply]
  refine Quotient.sound' ?_
  rw [MulAction.orbitRel_apply, ← MulAction.orbit_eq_iff, orbit_eq_affineConeOrbit hi hσ hx,
    ← affineConeOrbit_eq_orbit hi hσ F]

/-- The stabilizer of the distinguished point of a face `F` of a regular cone is the subtorus of
torus points that are trivial on the sublattice of characters vanishing on `F`. -/
theorem mem_stabilizer_distinguishedPoint_iff (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (F : σ.Face) (T : ComplexTorus N) :
    T ∈ MulAction.stabilizer (ComplexTorus N) (distinguishedPoint hi F) ↔
      ∀ m : N →+ ℤ, (∀ y, y ∈ F → hi.realCharacter m y = 0) → T m = 1 := by
  rw [MulAction.mem_stabilizer_iff]
  refine ⟨fun hT m hm ↦ ?_, fun hT ↦ ?_⟩
  · -- The stabilizer condition is triviality on the characters of the dual semigroup vanishing
    -- on `F`; these generate the sublattice of all characters vanishing on `F`, because `F` is cut
    -- out by a character `u` of the dual semigroup.
    have key (s : dualSemigroup hi σ) (hs : ∀ y, y ∈ F → hi.realCharacter (s : N →+ ℤ) y = 0) :
        T s = 1 := by
      have h := congrArg (fun x ↦ x (MonoidAlgebra.single (ofAdd s) 1)) hT
      simp only [ambient_smul_apply_single, distinguishedPoint_apply_single, ite_eq_left hs,
        mul_one] at h
      exact Units.ext h
    obtain ⟨u, hu, hFu⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi F.isFaceOf
    have huF (y : V) (hy : y ∈ F) : hi.realCharacter u y = 0 := by
      have hy' : y ∈ σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter u)) := by
        rw [hFu]
        exact hy
      exact hy'.2
    have hmF : m ∈ dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter u))) := by
      rw [hFu, mem_dualSemigroup]
      intro y hy
      rw [hm y hy]
    obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ.toIsToricCone.fg hu hmF
    have h₁ := key ⟨_, hn⟩ fun y hy ↦ by simp [hm y hy, huF y hy]
    rw [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow, key ⟨u, hu⟩ huF, one_pow,
      mul_one] at h₁
    exact h₁
  · refine AffineSemigroupComplexPoint.ext fun s ↦ ?_
    rw [ambient_smul_apply_single, distinguishedPoint_apply_single]
    split_ifs with hs
    · rw [hT s hs, Units.val_one, one_mul]
    · rw [mul_zero]

end TorusOrbit

end TauCeti.Toric
