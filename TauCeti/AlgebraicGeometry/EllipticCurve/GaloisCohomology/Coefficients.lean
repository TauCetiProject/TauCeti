/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.Topology.Algebra.GroupAction.ForcedDiscrete
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The Galois coefficient modules of an elliptic curve

Let `W` be a Weierstrass curve over a field `K`, `Kˢ` a separable closure of `K` and
`G_K = AbsoluteGaloisGroup K`. The Galois cohomology of an elliptic curve takes its coefficients
in two discrete `G_K`-modules, fixed here once and for all:

```text
W.PointCoeff = E(Kˢ),      W.TorsionCoeff m = E(Kˢ)[m],
```

with `G_K` acting on the coordinates of points. The first is a type synonym of
`TauCeti.ForcedDiscrete` applied to the points of the base change `W⁄Kˢ`, so it carries the
**discrete** topology imposed by that wrapper rather than by an instance on the point type
itself. Both modules are discrete `G_K`-modules in the sense continuous cohomology
asks for: the stabilizer of a point is open, because its coordinates lie in `Kˢ`, which is
algebraic over `K` (`WeierstrassCurve.PointCoeff.instContinuousSMul`).

For `m` invertible in `K`, multiplication by `m` gives the **Kummer sequence** of `W`,

```text
0 ⟶ E(Kˢ)[m] ⟶ E(Kˢ) ⟶ E(Kˢ) ⟶ 0,
```

as a `TauCeti.ContCohomology.DiscreteShortExact` (`WeierstrassCurve.kummerShortExact`), so that the
long exact sequence of continuous cohomology applies to it verbatim. Exactness on the right is the
divisibility of `E(Kˢ)` (`WeierstrassCurve.Affine.nsmul_surjective`), which is where invertibility
of `m` enters.

Finally `WeierstrassCurve.basePointEquivInvariants` identifies `H⁰(G_K, E(Kˢ))` with `E(K)`. The
two are different Lean types, so what is supplied is the canonical isomorphism, induced by the
inclusion `K → Kˢ`. It rests on the fixed field of `G_K` being `K`, which is why the separable
closure and not an algebraic closure is used: over an imperfect `K` the points of `E` fixed by the
automorphisms of an algebraic closure are the points over the perfect closure of `K`.

## Main definitions

* `WeierstrassCurve.PointCoeff`: the points of `W` over `Kˢ`, as a discrete `G_K`-module.
* `WeierstrassCurve.pointCoeffEquiv`: its identification with the points of `W⁄Kˢ`.
* `WeierstrassCurve.TorsionCoeff`: the `m`-torsion of `W.PointCoeff`, a discrete `G_K`-module.
* `WeierstrassCurve.torsionCoeffIncl`: the equivariant inclusion `E(Kˢ)[m] → E(Kˢ)`.
* `WeierstrassCurve.kummerShortExact`: the Kummer sequence `0 → E[m] → E → E → 0` of `W`.
* `WeierstrassCurve.basePointCoeff`: the inclusion `E(K) → E(Kˢ)`.
* `WeierstrassCurve.basePointEquivInvariants`: the isomorphism `E(K) ≅ H⁰(G_K, E(Kˢ))`.

## Main results

* `WeierstrassCurve.PointCoeff.instContinuousSMul`,
  `WeierstrassCurve.TorsionCoeff.instContinuousSMul`: the coefficients are discrete modules.
* `WeierstrassCurve.pointGaloisAction_apply_eq_smul`: the action is
  `WeierstrassCurve.pointGaloisAction`.
* `WeierstrassCurve.mem_H0_pointCoeff_iff`: a point of `E(Kˢ)` fixed by `G_K` comes from `E(K)`.

## Implementation notes

The construction follows the multiplicative coefficient modules of
`TauCeti/FieldTheory/GaloisCohomology/Coefficients.lean`: `WeierstrassCurve.PointCoeff`,
`WeierstrassCurve.kummerShortExact` and `WeierstrassCurve.basePointEquivInvariants` play the roles
of `TauCeti.UnitsCoeff`, `TauCeti.kummerShortExact` and `TauCeti.baseUnitsEquivInvariants` there.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.2 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-! ### The points over the separable closure -/

/-- **The points of `W` over a separable closure `Kˢ` of `K`**, as the coefficient module of the
Galois cohomology of `W`. It is a type synonym for `ForcedDiscrete (W⁄Kˢ).toAffine.Point`, so that
the discrete topology is the one imposed by `TauCeti.ForcedDiscrete`, and the action of `G_K` lives
on it and not on the point type. -/
def PointCoeff : Type _ := ForcedDiscrete (W⁄(SeparableClosure K)).toAffine.Point

open scoped Classical in
instance : AddCommGroup W.PointCoeff :=
  inferInstanceAs (AddCommGroup (ForcedDiscrete (W⁄(SeparableClosure K)).toAffine.Point))

instance : TopologicalSpace W.PointCoeff :=
  inferInstanceAs (TopologicalSpace (ForcedDiscrete (W⁄(SeparableClosure K)).toAffine.Point))

instance : DiscreteTopology W.PointCoeff :=
  inferInstanceAs (DiscreteTopology (ForcedDiscrete (W⁄(SeparableClosure K)).toAffine.Point))

open scoped Classical in
/-- The identification of `W.PointCoeff` with the points of `W` over `Kˢ`. -/
def pointCoeffEquiv : (W⁄(SeparableClosure K)).toAffine.Point ≃+ W.PointCoeff :=
  ForcedDiscrete.addEquiv _

/-! ### The Galois action -/

open scoped Classical in
/-- **`G_K` acts on `E(Kˢ)`** through the coordinates, by Mathlib's point map along each
automorphism. -/
instance : SMul (AbsoluteGaloisGroup K) W.PointCoeff where
  smul σ P := W.pointCoeffEquiv (Affine.Point.map σ.toAlgHom (W.pointCoeffEquiv.symm P))

open scoped Classical in
/-- **The Galois action on `E(Kˢ)` is the point map** along the automorphism. -/
@[simp]
theorem pointCoeffEquiv_symm_smul (σ : AbsoluteGaloisGroup K) (P : W.PointCoeff) :
    W.pointCoeffEquiv.symm (σ • P) = Affine.Point.map σ.toAlgHom (W.pointCoeffEquiv.symm P) :=
  (rfl)

open scoped Classical in
/-- The Galois action on a point of `W⁄Kˢ`, read in `W.PointCoeff`. -/
@[simp]
theorem smul_pointCoeffEquiv (σ : AbsoluteGaloisGroup K)
    (P : (W⁄(SeparableClosure K)).toAffine.Point) :
    σ • W.pointCoeffEquiv P = W.pointCoeffEquiv (Affine.Point.map σ.toAlgHom P) :=
  (rfl)

open scoped Classical in
instance : DistribMulAction (AbsoluteGaloisGroup K) W.PointCoeff where
  one_smul P := by
    obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
    rw [smul_pointCoeffEquiv]
    congr 1
    -- The identity automorphism keeps both coordinates, by definition of the point map.
    rcases P with _ | ⟨x, y, h⟩ <;> rfl
  mul_smul σ τ P := by
    obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
    rw [smul_pointCoeffEquiv, smul_pointCoeffEquiv, smul_pointCoeffEquiv, Affine.Point.map_map]
    rfl
  smul_zero σ := by
    rw [← W.pointCoeffEquiv.map_zero, smul_pointCoeffEquiv, map_zero]
  smul_add σ P Q := by
    obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
    obtain ⟨Q, rfl⟩ := W.pointCoeffEquiv.surjective Q
    rw [← map_add, smul_pointCoeffEquiv, smul_pointCoeffEquiv, smul_pointCoeffEquiv, map_add,
      map_add]

open scoped Classical in
/-- **The action is `WeierstrassCurve.pointGaloisAction`**, read in `W.PointCoeff`. -/
theorem pointGaloisAction_apply_eq_smul (σ : AbsoluteGaloisGroup K)
    (P : (W⁄(SeparableClosure K)).toAffine.Point) :
    Multiplicative.toAdd (W.pointGaloisAction σ) P =
      W.pointCoeffEquiv.symm (σ • W.pointCoeffEquiv P) := by
  rw [pointGaloisAction_apply, pointCoeffEquiv_symm_smul, AddEquiv.symm_apply_apply]

open scoped Classical in
/-- **`E(Kˢ)` is a discrete `G_K`-module**: the stabilizer of an affine point contains the
stabilizers of its two coordinates, which are open because `Kˢ` is algebraic over `K`. -/
instance PointCoeff.instContinuousSMul :
    ContinuousSMul (AbsoluteGaloisGroup K) W.PointCoeff := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun P => ?_
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  rcases P with _ | ⟨x, y, h⟩
  · convert isOpen_univ
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    rw [← Affine.Point.zero_def, map_zero, smul_zero]
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ x ⊓ MulAction.stabilizer _ y)
      (fun σ hσ => ?_) ?_
    · rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hσ
      rw [MulAction.mem_stabilizer_iff, smul_pointCoeffEquiv, Affine.Point.map_some]
      congr 1
      simp only [Affine.Point.some.injEq]
      exact ⟨hσ.1, hσ.2⟩
    · rw [Subgroup.coe_inf]
      exact (stabilizer_isOpen_of_isIntegral x).inter (stabilizer_isOpen_of_isIntegral y)

/-! ### The `m`-torsion -/

/-- **The `m`-torsion `E(Kˢ)[m]` of `W`**, as a coefficient module of the Galois cohomology of
`W`. Its topology is the subspace topology, which is discrete. -/
abbrev TorsionCoeff (m : ℕ) : Type _ := AddSubgroup.torsionBy W.PointCoeff m

variable {W} in
/-- The Galois action commutes with multiplication by `m`, so it preserves `E(Kˢ)[m]`. -/
theorem smul_mem_torsionCoeff {m : ℕ} (σ : AbsoluteGaloisGroup K) {P : W.PointCoeff}
    (hP : P ∈ AddSubgroup.torsionBy W.PointCoeff m) :
    σ • P ∈ AddSubgroup.torsionBy W.PointCoeff m := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← smul_comm, hP, smul_zero]

instance (m : ℕ) : DistribMulAction (AbsoluteGaloisGroup K) (W.TorsionCoeff m) :=
  (AddSubgroup.torsionBy W.PointCoeff m).restrictDistribMulAction fun σ _ => smul_mem_torsionCoeff σ

/-- The Galois action on `E(Kˢ)[m]` is the action on `E(Kˢ)`. -/
@[simp]
theorem coe_smul_torsionCoeff {m : ℕ} (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m) :
    ((σ • P : W.TorsionCoeff m) : W.PointCoeff) = σ • (P : W.PointCoeff) :=
  AddSubgroup.restrictDistribMulAction_coe_smul _ (fun σ _ => smul_mem_torsionCoeff σ) σ P

/-- **`E(Kˢ)[m]` is a discrete `G_K`-module**: the restriction of the continuous action on
`E(Kˢ)` to a stable subgroup is continuous. -/
instance TorsionCoeff.instContinuousSMul (m : ℕ) :
    ContinuousSMul (AbsoluteGaloisGroup K) (W.TorsionCoeff m) :=
  AddSubgroup.restrictDistribMulAction_continuousSMul _ fun σ _ => smul_mem_torsionCoeff σ

/-- The inclusion `E(Kˢ)[m] → E(Kˢ)`, as a `G_K`-equivariant homomorphism. -/
def torsionCoeffIncl (m : ℕ) : W.TorsionCoeff m →+[AbsoluteGaloisGroup K] W.PointCoeff where
  toFun := Subtype.val
  map_smul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)

@[simp]
theorem torsionCoeffIncl_apply {m : ℕ} (P : W.TorsionCoeff m) :
    W.torsionCoeffIncl m P = (P : W.PointCoeff) :=
  (rfl)

/-! ### The Kummer sequence -/

/-- **The Kummer sequence** `0 → E(Kˢ)[m] → E(Kˢ) → E(Kˢ) → 0` of `W`, for `m` invertible in
`K`. Exactness on the right is the divisibility of `E(Kˢ)` by `m`. -/
def kummerShortExact [W.IsElliptic] (m : ℕ) (hm : IsUnit (m : K)) :
    DiscreteShortExact (AbsoluteGaloisGroup K) (W.TorsionCoeff m) W.PointCoeff W.PointCoeff where
  incl := (AddSubgroup.torsionBy W.PointCoeff m).subtype
  proj := nsmulAddMonoidHom m
  incl_equivariant _ _ := (rfl)
  proj_equivariant σ P := smul_comm m σ P
  incl_injective := Subtype.val_injective
  proj_surjective P := by
    classical
    have hm' : ((m : ℕ) : SeparableClosure K) ≠ 0 := by
      rw [← map_natCast (algebraMap K (SeparableClosure K))]
      exact (map_ne_zero _).2 hm.ne_zero
    obtain ⟨Q, hQ⟩ := Affine.nsmul_surjective (W⁄(SeparableClosure K)).toAffine hm'
      (W.pointCoeffEquiv.symm P)
    refine ⟨W.pointCoeffEquiv Q, ?_⟩
    rw [nsmulAddMonoidHom_apply, ← map_nsmul]
    exact (congrArg W.pointCoeffEquiv hQ).trans (W.pointCoeffEquiv.apply_symm_apply P)
  exact P := by
    rw [nsmulAddMonoidHom_apply, ← AddSubgroup.torsionBy.nsmul_iff]
    exact ⟨fun hP => ⟨⟨P, hP⟩, rfl⟩, fun ⟨Q, hQ⟩ => hQ ▸ Q.2⟩

@[simp]
theorem kummerShortExact_incl [W.IsElliptic] (m : ℕ) (hm : IsUnit (m : K)) :
    (W.kummerShortExact m hm).incl = (AddSubgroup.torsionBy W.PointCoeff m).subtype :=
  (rfl)

@[simp]
theorem kummerShortExact_proj [W.IsElliptic] (m : ℕ) (hm : IsUnit (m : K)) :
    (W.kummerShortExact m hm).proj = nsmulAddMonoidHom m :=
  (rfl)

/-- The equivariant inclusion of the Kummer sequence is `WeierstrassCurve.torsionCoeffIncl`. -/
@[simp]
theorem kummerShortExact_inclDistribMulActionHom [W.IsElliptic] (m : ℕ) (hm : IsUnit (m : K)) :
    (W.kummerShortExact m hm).inclDistribMulActionHom = W.torsionCoeffIncl m := by
  ext P
  rw [DiscreteShortExact.inclDistribMulActionHom_apply, kummerShortExact_incl,
    torsionCoeffIncl_apply, AddSubgroup.coe_subtype]

/-! ### The invariants of `E(Kˢ)` -/

variable [DecidableEq K]

open scoped Classical in
/-- **The inclusion `E(K) → E(Kˢ)`**, induced by the inclusion of `K` into `Kˢ`. -/
def basePointCoeff : W.toAffine.Point →+ W.PointCoeff :=
  W.pointCoeffEquiv.toAddMonoidHom.comp <|
    (Affine.Point.map (W' := W.toAffine) (Algebra.ofId K (SeparableClosure K))).comp
      (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom

open scoped Classical in
/-- The inclusion `E(K) → E(Kˢ)` keeps the coordinates of an affine point. -/
@[simp]
theorem basePointCoeff_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    W.basePointCoeff (.some x y h) =
      W.pointCoeffEquiv (.some (algebraMap K (SeparableClosure K) x)
        (algebraMap K (SeparableClosure K) y)
        ((W.toAffine.baseChange_nonsingular (Algebra.ofId K (SeparableClosure K)).injective
          x y).2 h)) := by
  simp only [basePointCoeff, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Affine.Point.equivBaseChangeSelf_some, Affine.Point.map_some]
  rfl

/-- The inclusion `E(K) → E(Kˢ)` is injective. -/
theorem basePointCoeff_injective : Function.Injective W.basePointCoeff := by
  classical
  exact W.pointCoeffEquiv.injective.comp <| (Affine.Point.map_injective _).comp
    (Affine.Point.equivBaseChangeSelf W.toAffine).injective

/-- **A point of `E(K)` is fixed by `G_K`** after mapping into `E(Kˢ)`. -/
theorem smul_basePointCoeff (σ : AbsoluteGaloisGroup K) (P : W.toAffine.Point) :
    σ • W.basePointCoeff P = W.basePointCoeff P := by
  classical
  rw [basePointCoeff, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, smul_pointCoeffEquiv,
    AddMonoidHom.comp_apply, Affine.Point.map_map]
  rw [Subsingleton.elim (σ.toAlgHom.comp (Algebra.ofId K (SeparableClosure K)))
    (Algebra.ofId K (SeparableClosure K))]

/-- **A point of `E(Kˢ)` fixed by the whole Galois group comes from `E(K)`.** This is the
fixed-field theorem `InfiniteGalois.mem_range_algebraMap_iff_fixed` for the separable closure,
applied to the two coordinates of the point. -/
theorem mem_H0_pointCoeff_iff {P : W.PointCoeff} :
    P ∈ H0 (AbsoluteGaloisGroup K) W.PointCoeff ↔
      ∃ Q : W.toAffine.Point, W.basePointCoeff Q = P := by
  classical
  rw [FixedPoints.mem_addSubgroup]
  refine ⟨fun hP => ?_, fun ⟨Q, hQ⟩ σ => hQ ▸ W.smul_basePointCoeff σ Q⟩
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, by rw [map_zero, ← Affine.Point.zero_def, map_zero]⟩
  · -- Both coordinates are fixed by `G_K`, so they come from `K`.
    have hfix : ∀ σ : AbsoluteGaloisGroup K, σ x = x ∧ σ y = y := fun σ => by
      have h := hP σ
      rw [smul_pointCoeffEquiv, Affine.Point.map_some] at h
      simpa only [Affine.Point.some.injEq, AlgEquiv.coe_toAlgHom] using
        W.pointCoeffEquiv.injective h
    obtain ⟨x₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 fun σ => (hfix σ).1
    obtain ⟨y₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 fun σ => (hfix σ).2
    have h₀ : W.toAffine.Nonsingular x₀ y₀ :=
      (W.toAffine.baseChange_nonsingular (Algebra.ofId K (SeparableClosure K)).injective
        x₀ y₀).1 h
    exact ⟨.some x₀ y₀ h₀, by rw [basePointCoeff_some]⟩

/-- **The invariants of `E(Kˢ)` are the points of `E(K)`**, that is `H⁰(G_K, E(Kˢ)) ≅ E(K)`. The
two sides are different Lean types, so this canonical isomorphism, and not an equality, is what a
cohomological construction starting from `E(K)` goes through, the Kummer map among them. -/
def basePointEquivInvariants : W.toAffine.Point ≃+ H0 (AbsoluteGaloisGroup K) W.PointCoeff :=
  AddEquiv.ofBijective
    (W.basePointCoeff.codRestrict _ fun P => W.mem_H0_pointCoeff_iff.2 ⟨P, rfl⟩)
    ⟨fun P Q h => W.basePointCoeff_injective (congrArg Subtype.val h), fun P => by
      obtain ⟨Q, hQ⟩ := W.mem_H0_pointCoeff_iff.1 P.2
      exact ⟨Q, Subtype.ext hQ⟩⟩

@[simp]
theorem coe_basePointEquivInvariants (P : W.toAffine.Point) :
    (W.basePointEquivInvariants P : W.PointCoeff) = W.basePointCoeff P :=
  (rfl)

end WeierstrassCurve
