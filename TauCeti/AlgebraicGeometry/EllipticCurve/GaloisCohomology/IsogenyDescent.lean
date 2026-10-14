/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
-- Proof-only: separability of an isogeny survives base change to `Kˢ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
-- Proof-only: a separable isogeny is onto on points over a separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# The Kummer sequence of an isogeny and the `φ`-descent sequence

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, `Kˢ` a separable closure and
`G_K` its Galois group. The isogeny acts on the points over `Kˢ`, and this action commutes with
`G_K` because `φ` is defined over `K` (`TauCeti.Isogeny.Hom.pointCoeffMap`). Its kernel
`E₁(Kˢ)[φ]` is therefore a discrete `G_K`-module (`TauCeti.Isogeny.Hom.KerCoeff`). When `φ` is
separable it is onto on points over `Kˢ`, and the **Kummer sequence of `φ`**

```text
0 ⟶ E₁(Kˢ)[φ] ⟶ E₁(Kˢ) ⟶ E₂(Kˢ) ⟶ 0
```

is a short exact sequence of discrete `G_K`-modules (`TauCeti.Isogeny.kummerShortExact`). Its
degree-zero connecting map, read on `E₂(K)` through `WeierstrassCurve.basePointEquivInvariants`,
is the **Kummer map** `E₂(K) → H¹(G_K, E₁[φ])`, and the long exact sequence of continuous
cohomology gives the **`φ`-descent sequence** (Silverman X.4)

```text
0 ⟶ E₂(K) ⧸ φ(E₁(K)) ⟶ H¹(G_K, E₁[φ]) ⟶ H¹(G_K, E₁)[φ] ⟶ 0,
```

where `H¹(G_K, E₁)[φ]` is the kernel of the map `H¹(G_K, E₁) → H¹(G_K, E₂)` induced by `φ`. The
Kummer class of `P` is represented by `σ ↦ σ Q - Q` for any `Q ∈ E₁(Kˢ)` with `φ Q = P`.

This is the descent sequence of `WeierstrassCurve.kummerMap` with multiplication by `m` replaced
by an arbitrary separable isogeny. Separability is what makes `φ` onto on points over `Kˢ`; for
`[m]` it is the invertibility of `m` in `K`. Selmer groups attached to `φ` and to its dual are cut
out of the middle term by local conditions, as in `WeierstrassCurve.selmerGroup`.

## Main definitions

* `TauCeti.Isogeny.Hom.pointCoeffMap`: the `G_K`-equivariant action `E₁(Kˢ) → E₂(Kˢ)` of a
  morphism `f : W₁ → W₂` over `K`.
* `TauCeti.Isogeny.Hom.KerCoeff`: its kernel `E₁(Kˢ)[f]`, a discrete `G_K`-module.
* `TauCeti.Isogeny.Hom.kummerCocycle`: the cocycle `σ ↦ σ Q - Q` attached to a point `Q` over `Kˢ`
  whose image is rational.
* `TauCeti.Isogeny.kummerShortExact`: the Kummer sequence of a separable isogeny.
* `TauCeti.Isogeny.kummerMap`: the Kummer map `E₂(K) → H¹(G_K, E₁[φ])`.
* `TauCeti.Isogeny.kummerClassMap`: the induced map on `E₂(K) ⧸ φ(E₁(K))`.
* `TauCeti.Isogeny.kerCoeffInclH1`: the map `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ]`.

## Main results

* `TauCeti.Isogeny.Hom.pointCoeffMap_basePointCoeff`: the action over `Kˢ` extends the action on
  `E₁(K)`.
* `TauCeti.Isogeny.kummerMap_eq_H1pi`: the Kummer class of `P` is the class of `σ ↦ σ Q - Q`.
* `TauCeti.Isogeny.ker_kummerMap`: the kernel of the Kummer map is `φ(E₁(K))`.
* `TauCeti.Isogeny.kummerClassMap_injective`, `TauCeti.Isogeny.exact_kummerClassMap_kerCoeffInclH1`
  and `TauCeti.Isogeny.kerCoeffInclH1_surjective`: the `φ`-descent sequence.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

namespace TauCeti.Isogeny.Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-! ### The action on the points over a separable closure -/

/-- The base change of a morphism `f : W₁ → W₂` to a separable closure `Kˢ` of `K`, typed between
the base changes `W₁⁄Kˢ` and `W₂⁄Kˢ` whose points are the Galois coefficient modules. -/
abbrev mapSeparableClosure (f : Hom W₁.toAffine W₂.toAffine) :
    Hom (W₁⁄(SeparableClosure K)).toAffine (W₂⁄(SeparableClosure K)).toAffine :=
  f.map (algebraMap K (SeparableClosure K))

open scoped Classical in
/-- **The action of a morphism over `K` on the points over `Kˢ`**, as a `G_K`-equivariant
homomorphism `E₁(Kˢ) → E₂(Kˢ)`. Equivariance holds because the morphism is defined over `K`
(`TauCeti.Isogeny.Hom.pointMap_map_algebraMap_map`). -/
def pointCoeffMap (f : Hom W₁.toAffine W₂.toAffine) :
    W₁.PointCoeff →+[AbsoluteGaloisGroup K] W₂.PointCoeff where
  toFun P := W₂.pointCoeffEquiv (f.mapSeparableClosure.pointMap (W₁.pointCoeffEquiv.symm P))
  map_smul' σ P := by
    rw [MonoidHom.id_apply, smul_pointCoeffEquiv]
    exact congrArg W₂.pointCoeffEquiv ((congrArg _ (W₁.pointCoeffEquiv_symm_smul σ P)).trans
      (pointMap_map_algebraMap_map f σ.toAlgHom _))
  map_zero' := by rw [map_zero, pointMap_zero, map_zero]
  map_add' P Q := by rw [_root_.map_add, pointMap_add, _root_.map_add]

open scoped Classical in
/-- The action on `E₁(Kˢ)`, read on the points of `W₁⁄Kˢ`, is the base change of `f` to `Kˢ`. -/
@[simp]
theorem pointCoeffEquiv_symm_pointCoeffMap (f : Hom W₁.toAffine W₂.toAffine)
    (P : W₁.PointCoeff) :
    W₂.pointCoeffEquiv.symm (f.pointCoeffMap P) =
      f.mapSeparableClosure.pointMap (W₁.pointCoeffEquiv.symm P) :=
  W₂.pointCoeffEquiv.symm_apply_apply _

open scoped Classical in
/-- The action on a point of `W₁⁄Kˢ`, read in `W₁.PointCoeff`. -/
@[simp]
theorem pointCoeffMap_pointCoeffEquiv (f : Hom W₁.toAffine W₂.toAffine)
    (P : (W₁⁄(SeparableClosure K)).toAffine.Point) :
    f.pointCoeffMap (W₁.pointCoeffEquiv P) =
      W₂.pointCoeffEquiv (f.mapSeparableClosure.pointMap P) := by
  rw [← W₂.pointCoeffEquiv.apply_symm_apply (f.pointCoeffMap _),
    pointCoeffEquiv_symm_pointCoeffMap, AddEquiv.symm_apply_apply]

/-- **The action over `Kˢ` extends the action on rational points**: a morphism over `K` sends the
image in `E₁(Kˢ)` of a point of `E₁(K)` to the image of its value in `E₂(K)`. -/
@[simp]
theorem pointCoeffMap_basePointCoeff [DecidableEq K] (f : Hom W₁.toAffine W₂.toAffine)
    (P : W₁.toAffine.Point) :
    f.pointCoeffMap (W₁.basePointCoeff P) = W₂.basePointCoeff (f.pointMap P) := by
  classical
  rw [basePointCoeff_eq_pointCoeffEquiv_mapAlong, basePointCoeff_eq_pointCoeffEquiv_mapAlong]
  exact (pointCoeffMap_pointCoeffEquiv f _).trans (congrArg W₂.pointCoeffEquiv (pointMap_map f _ P))

/-! ### The kernel -/

/-- **The kernel `E₁(Kˢ)[f]`** of the action of a morphism `f : W₁ → W₂` over `K` on the points
over `Kˢ`, as a coefficient module of the Galois cohomology of `W₁`. Its topology is the subspace
topology, which is discrete. -/
abbrev KerCoeff (f : Hom W₁.toAffine W₂.toAffine) : Type _ :=
  (f.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker

variable {f : Hom W₁.toAffine W₂.toAffine}

/-- The Galois action commutes with `f`, so it preserves `E₁(Kˢ)[f]`. -/
theorem smul_mem_kerCoeff (σ : AbsoluteGaloisGroup K) {P : W₁.PointCoeff}
    (hP : P ∈ (f.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker) :
    σ • P ∈ (f.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass] at hP ⊢
  rw [map_smul, hP, smul_zero]

instance : DistribMulAction (AbsoluteGaloisGroup K) f.KerCoeff :=
  (f.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker.restrictDistribMulAction
    fun σ _ ↦ smul_mem_kerCoeff σ

/-- The Galois action on `E₁(Kˢ)[f]` is the action on `E₁(Kˢ)`. -/
@[simp]
theorem coe_smul_kerCoeff (σ : AbsoluteGaloisGroup K) (P : f.KerCoeff) :
    ((σ • P : f.KerCoeff) : W₁.PointCoeff) = σ • (P : W₁.PointCoeff) :=
  AddSubgroup.restrictDistribMulAction_coe_smul _ (fun σ _ ↦ smul_mem_kerCoeff σ) σ P

/-- **`E₁(Kˢ)[f]` is a discrete `G_K`-module**: the restriction of the continuous action on
`E₁(Kˢ)` to a stable subgroup is continuous. -/
instance KerCoeff.instContinuousSMul : ContinuousSMul (AbsoluteGaloisGroup K) f.KerCoeff :=
  AddSubgroup.restrictDistribMulAction_continuousSMul _ fun σ _ ↦ smul_mem_kerCoeff σ

variable (f) in
/-- The inclusion `E₁(Kˢ)[f] → E₁(Kˢ)`, as a `G_K`-equivariant homomorphism. -/
def kerCoeffIncl : f.KerCoeff →+[AbsoluteGaloisGroup K] W₁.PointCoeff where
  toFun := Subtype.val
  map_smul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)

/-- The inclusion `E₁(Kˢ)[f] → E₁(Kˢ)` forgets membership in the kernel. -/
@[simp]
theorem kerCoeffIncl_apply (P : f.KerCoeff) : f.kerCoeffIncl P = (P : W₁.PointCoeff) :=
  (rfl)

/-! ### The Kummer cocycle -/

variable [DecidableEq K]

/-- **The Kummer difference lies in the kernel**: if `f Q` is the image of a point of `E₂(K)`,
then `σ Q - Q` is killed by `f`, because `G_K` fixes `f Q`. -/
theorem smul_sub_mem_kerCoeff {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : f.pointCoeffMap Q = W₂.basePointCoeff P) (σ : AbsoluteGaloisGroup K) :
    σ • Q - Q ∈ (f.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, _root_.map_sub, map_smul, hQ,
    smul_basePointCoeff, sub_self]

/-- **The Kummer cocycle** `σ ↦ σ Q - Q` attached to a point `Q` of `E₁(Kˢ)` with `f Q` in
`E₂(K)`. -/
def kummerCocycle {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : f.pointCoeffMap Q = W₂.basePointCoeff P) : AbsoluteGaloisGroup K → f.KerCoeff :=
  fun σ ↦ ⟨σ • Q - Q, smul_sub_mem_kerCoeff hQ σ⟩

/-- The Kummer cocycle takes the value `σ Q - Q` at `σ`. -/
@[simp]
theorem coe_kummerCocycle {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : f.pointCoeffMap Q = W₂.basePointCoeff P) (σ : AbsoluteGaloisGroup K) :
    (kummerCocycle hQ σ : W₁.PointCoeff) = σ • Q - Q :=
  (rfl)

/-- **The Kummer cocycle is a continuous `1`-cocycle**: its image in `E₁(Kˢ)` is the coboundary
of `Q`. -/
theorem kummerCocycle_mem_Z1 {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : f.pointCoeffMap Q = W₂.basePointCoeff P) :
    kummerCocycle hQ ∈ Z1 (AbsoluteGaloisGroup K) f.KerCoeff :=
  mem_Z1_of_injective_comp_eq_d0
    (φ := (f.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker.subtype)
    Subtype.val_injective (fun _ _ ↦ rfl) fun σ ↦ by
      rw [AddSubgroup.coe_subtype, coe_kummerCocycle]

end TauCeti.Isogeny.Hom

namespace TauCeti.Isogeny

open Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]

/-! ### The Kummer sequence of a separable isogeny -/

open scoped Classical in
/-- **A separable isogeny is onto on points over `Kˢ`**: it stays separable after base change, and
a separable isogeny over a separably closed field is surjective on points. -/
theorem pointCoeffMap_ofIsogeny_surjective : Function.Surjective (ofIsogeny φ).pointCoeffMap := by
  intro P
  have := isSeparable_map φ (algebraMap K (SeparableClosure K))
  have := (W₂⁄(SeparableClosure K)).toAffine.isIntegrallyClosed_coordinateRing
  obtain ⟨Q, hQ⟩ := (φ.map (algebraMap K (SeparableClosure K))).toPointHom_surjective
    (W₂.pointCoeffEquiv.symm P)
  refine ⟨W₁.pointCoeffEquiv Q, (pointCoeffMap_pointCoeffEquiv _ _).trans ?_⟩
  rw [← W₂.pointCoeffEquiv.apply_symm_apply P, ← hQ]
  exact congrArg W₂.pointCoeffEquiv ((congrArg (fun g ↦ g.pointMap Q) (ofIsogeny_map φ _)).trans
    (pointMap_ofIsogeny_eq_toPointHom _ Q))

/-- **The Kummer sequence** `0 → E₁(Kˢ)[φ] → E₁(Kˢ) → E₂(Kˢ) → 0` of a separable isogeny `φ`.
Exactness on the right is the surjectivity of `φ` on points over `Kˢ`. -/
def kummerShortExact :
    DiscreteShortExact (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff W₁.PointCoeff
      W₂.PointCoeff where
  incl := ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker.subtype
  proj := (ofIsogeny φ).pointCoeffMap
  incl_equivariant _ _ := (rfl)
  proj_equivariant σ P := map_smul (ofIsogeny φ).pointCoeffMap σ P
  incl_injective := Subtype.val_injective
  proj_surjective := pointCoeffMap_ofIsogeny_surjective φ
  exact := by rw [AddMonoidHom.exact_iff, AddSubgroup.range_subtype]

/-- The inclusion of the Kummer sequence is the inclusion of the kernel of `φ`. -/
@[simp]
theorem kummerShortExact_incl :
    φ.kummerShortExact.incl =
      ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker.subtype :=
  (rfl)

/-- The projection of the Kummer sequence is the action of `φ` on `E₁(Kˢ)`. -/
@[simp]
theorem kummerShortExact_proj :
    φ.kummerShortExact.proj = ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff) :=
  (rfl)

/-- The equivariant inclusion of the Kummer sequence is `TauCeti.Isogeny.Hom.kerCoeffIncl`. -/
@[simp]
theorem kummerShortExact_inclDistribMulActionHom :
    φ.kummerShortExact.inclDistribMulActionHom = (ofIsogeny φ).kerCoeffIncl := by
  ext P
  rw [DiscreteShortExact.inclDistribMulActionHom_apply, Isogeny.kummerShortExact_incl,
    kerCoeffIncl_apply, AddSubgroup.coe_subtype]

/-- The equivariant projection of the Kummer sequence is `TauCeti.Isogeny.Hom.pointCoeffMap`. -/
@[simp]
theorem kummerShortExact_projDistribMulActionHom :
    φ.kummerShortExact.projDistribMulActionHom = (ofIsogeny φ).pointCoeffMap := by
  ext P
  rw [DiscreteShortExact.projDistribMulActionHom_apply, Isogeny.kummerShortExact_proj,
    AddMonoidHom.coe_ofClass]

/-! ### The Kummer map -/

variable [DecidableEq K]

/-- **The Kummer map** `E₂(K) → H¹(G_K, E₁[φ])` of a separable isogeny `φ : W₁ → W₂`: the
degree-zero connecting homomorphism of its Kummer sequence, read on `E₂(K)` through the
identification of `E₂(K)` with the invariants of `E₂(Kˢ)`. -/
def kummerMap : W₂.toAffine.Point →+ H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff :=
  φ.kummerShortExact.explicitDelta0.comp W₂.basePointEquivInvariants.toAddMonoidHom

/-- **The Kummer map is the degree-zero connecting homomorphism** of the Kummer sequence, read on
`P` through the identification of `E₂(K)` with the invariants of `E₂(Kˢ)`. -/
@[simp]
theorem kummerMap_apply (P : W₂.toAffine.Point) :
    φ.kummerMap P = φ.kummerShortExact.explicitDelta0 (W₂.basePointEquivInvariants P) :=
  (rfl)

variable {φ} in
/-- **The Kummer class of `P` is represented by `σ ↦ σ Q - Q`**, for any `Q ∈ E₁(Kˢ)` with
`φ Q = P` (Silverman X.4). Such a `Q` exists because `φ` is onto on points over `Kˢ`. -/
theorem kummerMap_eq_H1pi {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : (ofIsogeny φ).pointCoeffMap Q = W₂.basePointCoeff P) :
    φ.kummerMap P =
      H1pi (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
        ⟨kummerCocycle hQ, kummerCocycle_mem_Z1 hQ⟩ :=
  (φ.kummerMap_apply P).trans <| φ.kummerShortExact.explicitDelta0_apply _ (b := Q)
    (by rw [Isogeny.kummerShortExact_proj, AddMonoidHom.coe_ofClass,
      coe_basePointEquivInvariants, hQ])
    fun σ ↦ by
      rw [Isogeny.kummerShortExact_incl, AddSubgroup.coe_subtype, Hom.coe_kummerCocycle]

/-- **`φ` on the invariants of `E₁(Kˢ)` is `φ` on `E₁(K)`.** This is the commuting square that
turns exactness of the long exact sequence at `H⁰(G_K, E₂(Kˢ))` into the computation of the
kernel of the Kummer map. -/
theorem explicitCoeff0_basePointEquivInvariants (P : W₁.toAffine.Point) :
    explicitCoeff0 (AbsoluteGaloisGroup K) W₁.PointCoeff
        φ.kummerShortExact.projDistribMulActionHom (W₁.basePointEquivInvariants P) =
      W₂.basePointEquivInvariants ((ofIsogeny φ).pointMap P) :=
  Subtype.ext <| by
    rw [coe_explicitCoeff0, Isogeny.kummerShortExact_projDistribMulActionHom,
      coe_basePointEquivInvariants, coe_basePointEquivInvariants, pointCoeffMap_basePointCoeff]

/-- **The kernel of the Kummer map is `φ(E₁(K))`.** -/
theorem ker_kummerMap : φ.kummerMap.ker = (ofIsogeny φ).pointMapHom.range := by
  ext P
  rw [AddMonoidHom.mem_ker, kummerMap_apply, ← AddMonoidHom.mem_ker,
    ← φ.kummerShortExact.explicitLongExact_H0C, AddMonoidHom.mem_range, AddMonoidHom.mem_range]
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨Q, hQ⟩ ↦ ⟨W₁.basePointEquivInvariants Q, ?_⟩⟩
  · obtain ⟨Q, rfl⟩ := W₁.basePointEquivInvariants.surjective u
    rw [Isogeny.explicitCoeff0_basePointEquivInvariants] at hu
    exact ⟨Q, by rw [pointMapHom_apply]; exact W₂.basePointEquivInvariants.injective hu⟩
  · rw [Isogeny.explicitCoeff0_basePointEquivInvariants, ← hQ, pointMapHom_apply]

variable {φ} in
/-- **A point has trivial Kummer class exactly when it lies in `φ(E₁(K))`.** -/
theorem kummerMap_eq_zero_iff {P : W₂.toAffine.Point} :
    φ.kummerMap P = 0 ↔ ∃ Q : W₁.toAffine.Point, (ofIsogeny φ).pointMap Q = P := by
  simp only [← AddMonoidHom.mem_ker, ker_kummerMap, AddMonoidHom.mem_range, pointMapHom_apply]

/-! ### The `φ`-descent sequence -/

/-- **The Kummer map on `E₂(K) ⧸ φ(E₁(K))`**, the first map of the `φ`-descent sequence. It is
injective (`TauCeti.Isogeny.kummerClassMap_injective`). -/
def kummerClassMap :
    W₂.toAffine.Point ⧸ (ofIsogeny φ).pointMapHom.range →+
      H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff :=
  QuotientAddGroup.lift _ φ.kummerMap φ.ker_kummerMap.ge

/-- The quotient Kummer map agrees with `TauCeti.Isogeny.kummerMap` on representatives. -/
@[simp]
theorem kummerClassMap_mk (P : W₂.toAffine.Point) :
    φ.kummerClassMap (QuotientAddGroup.mk P) = φ.kummerMap P :=
  (rfl)

/-- **`E₂(K) ⧸ φ(E₁(K))` injects into `H¹(G_K, E₁[φ])`**, the kernel of the Kummer map being
exactly `φ(E₁(K))`. -/
theorem kummerClassMap_injective : Function.Injective φ.kummerClassMap :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 φ.ker_kummerMap.symm

/-- **The image of the Kummer map is the kernel of `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)`.** -/
theorem range_kummerMap :
    φ.kummerMap.range =
      (explicitCoeff1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (ofIsogeny φ).kerCoeffIncl
        continuous_of_discreteTopology).ker := by
  rw [← Isogeny.kummerShortExact_inclDistribMulActionHom φ,
    ← φ.kummerShortExact.explicitLongExact_H1A]
  ext c
  refine ⟨fun ⟨P, hP⟩ ↦ ⟨_, hP⟩, fun ⟨u, hu⟩ ↦ ?_⟩
  obtain ⟨P, rfl⟩ := W₂.basePointEquivInvariants.surjective u
  exact ⟨P, hu⟩

omit [DecidableEq K] in
/-- **The image of `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)` is the kernel of the map
`H¹(G_K, E₁) → H¹(G_K, E₂)` induced by `φ`**, the last exactness statement of the `φ`-descent
sequence. -/
theorem range_explicitCoeff1_kerCoeffIncl :
    (explicitCoeff1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (ofIsogeny φ).kerCoeffIncl
        continuous_of_discreteTopology).range =
      (explicitCoeff1 (AbsoluteGaloisGroup K) W₁.PointCoeff (ofIsogeny φ).pointCoeffMap
        continuous_of_discreteTopology).ker := by
  have := φ.kummerShortExact.explicitLongExact_H1B
  rwa [Isogeny.kummerShortExact_inclDistribMulActionHom,
    Isogeny.kummerShortExact_projDistribMulActionHom] at this

omit [DecidableEq K] in
/-- **The map `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ]`**, the last map of the `φ`-descent sequence: the
map induced by the inclusion `E₁(Kˢ)[φ] → E₁(Kˢ)`, with values in the kernel `H¹(G_K, E₁)[φ]` of
the map induced by `φ`. It is surjective (`TauCeti.Isogeny.kerCoeffInclH1_surjective`), with
kernel the image of the Kummer map (`TauCeti.Isogeny.exact_kummerClassMap_kerCoeffInclH1`). -/
def kerCoeffInclH1 :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      (explicitCoeff1 (AbsoluteGaloisGroup K) W₁.PointCoeff (ofIsogeny φ).pointCoeffMap
        continuous_of_discreteTopology).ker :=
  (explicitCoeff1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (ofIsogeny φ).kerCoeffIncl
      continuous_of_discreteTopology).codRestrict _ fun c ↦ by
    rw [← range_explicitCoeff1_kerCoeffIncl φ]
    exact ⟨c, rfl⟩

omit [DecidableEq K] in
/-- `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ]` is the map induced by the inclusion `E₁(Kˢ)[φ] → E₁(Kˢ)`. -/
@[simp]
theorem coe_kerCoeffInclH1 (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    (φ.kerCoeffInclH1 c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) =
      explicitCoeff1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (ofIsogeny φ).kerCoeffIncl
        continuous_of_discreteTopology c :=
  (rfl)

omit [DecidableEq K] in
/-- **`H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ]` is surjective**, the right end of the `φ`-descent
sequence. -/
theorem kerCoeffInclH1_surjective : Function.Surjective φ.kerCoeffInclH1 := by
  rintro ⟨c, hc⟩
  rw [← range_explicitCoeff1_kerCoeffIncl φ] at hc
  obtain ⟨d, rfl⟩ := hc
  exact ⟨d, rfl⟩

/-- **The `φ`-descent sequence is exact at `H¹(G_K, E₁[φ])`**: the kernel of
`H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ]` is the image of `E₂(K) ⧸ φ(E₁(K))` under the Kummer map.
Together with `TauCeti.Isogeny.kummerClassMap_injective` and
`TauCeti.Isogeny.kerCoeffInclH1_surjective` this is the short exact sequence
`0 → E₂(K) ⧸ φ(E₁(K)) → H¹(G_K, E₁[φ]) → H¹(G_K, E₁)[φ] → 0`. -/
theorem exact_kummerClassMap_kerCoeffInclH1 :
    Function.Exact φ.kummerClassMap φ.kerCoeffInclH1 := by
  rw [AddMonoidHom.exact_iff, kerCoeffInclH1, AddMonoidHom.ker_codRestrict, ← range_kummerMap φ]
  ext c
  refine ⟨fun ⟨P, hP⟩ ↦ ⟨QuotientAddGroup.mk P, hP⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | _ P => exact ⟨P, hx⟩

end TauCeti.Isogeny
