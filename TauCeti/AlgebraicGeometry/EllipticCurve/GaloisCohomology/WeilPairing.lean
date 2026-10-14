/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.NatCast
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.RootsOfUnity
public import TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# The Weil pairing on the Galois coefficient modules of an elliptic curve

Let `W` be an elliptic curve over a field `K` and `m` a natural number invertible in `K`. The Weil
pairing `e_m` of `W` over the separable closure `Kˢ` is a pairing on the coefficient module
`E(Kˢ)[m]` (`WeierstrassCurve.TorsionCoeff`) with values in the roots of unity `μ_m`
(`TauCeti.KummerCoeff`), and it is `G_K`-equivariant. So a `K`-rational point `T` of order
dividing `m` gives a map of discrete `G_K`-modules

```text
W.weilPairingCoeff m hm T : E(Kˢ)[m] → μ_m,    P ↦ e_m(P, T),
```

and hence a map `H¹(G_K, E[m]) → H¹(G_K, μ_m)` into the group which Kummer theory identifies with
`Kˣ ⧸ (Kˣ)ᵐ` (`TauCeti.kummerIso`). These maps are natural in the field: restriction along a field
extension `L / K` commutes with them, the roots of unity being restricted along the same embedding
of separable closures (`WeierstrassCurve.explicitMap1_explicitCoeff1_weilPairingCoeff`).

When `E[m] ⊆ E(K)`, that is when `G_K` fixes every point of `E(Kˢ)[m]`, these maps together
detect every class: a class of `H¹(G_K, E[m])` which dies in `H¹(G_K, μ_m)` under every
`weilPairingCoeff T` is zero (`WeierstrassCurve.explicitCoeff1_weilPairingCoeff_injective`).
Indeed `G_K` then acts trivially on `μ_m` as well, so a class dying in `H¹(G_K, μ_m)` is a cocycle
killed by `e_m(·, T)`, and the Weil pairing is nondegenerate. This is how the Galois cohomology of
`E[m]` over a field containing `E[m]` is reduced to Kummer theory, the step on which the weak
Mordell–Weil theorem and the finiteness of the `m`-Selmer group rest: over a number field the
classes unramified outside a finite set `S` of places are then controlled by the finite group
`K(S, m)` (Silverman VIII.1.5, VIII.1.6 and X.4.2).

## Main definitions

* `WeierstrassCurve.torsionCoeffWeilPairing`: the Weil pairing `E(Kˢ)[m] × E(Kˢ)[m] → μ_m`.
* `WeierstrassCurve.weilPairingCoeff`: for `T ∈ E(K)[m]`, the equivariant map
  `E(Kˢ)[m] → μ_m`, `P ↦ e_m(P, T)`.

## Main results

* `WeierstrassCurve.torsionCoeffWeilPairing_smul`: the Weil pairing is `G_K`-equivariant.
* `WeierstrassCurve.torsionCoeffWeilPairing_torsionCoeffBaseChange`: the Weil pairing commutes with
  the maps on torsion and on roots of unity induced by an embedding `Kˢ → Lˢ` of separable closures.
* `WeierstrassCurve.torsionCoeffWeilPairing_nondegenerate`: the Weil pairing is nondegenerate.
* `WeierstrassCurve.explicitMap1_explicitCoeff1_weilPairingCoeff`: restriction to a field
  extension commutes with the maps `H¹(G, E[m]) → H¹(G, μ_m)`.
* `WeierstrassCurve.explicitCoeff1_weilPairingCoeff_injective`: if `G_K` fixes `E(Kˢ)[m]`, the
  maps `H¹(G_K, E[m]) → H¹(G_K, μ_m)` attached to the points of `E(K)[m]` are jointly injective.
* `WeierstrassCurve.finite_of_forall_finite_image_explicitCoeff1_weilPairingCoeff`: if `G_K` fixes
  `E(Kˢ)[m]`, a set of classes of `H¹(G_K, E[m])` with finite images in `H¹(G_K, μ_m)` is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1, VIII.1, X.1 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K))

include hm in
/-- An integer invertible in `K` is nonzero. -/
private theorem neZero_of_isUnit : NeZero m :=
  NeZero.of_neZero_natCast K (h := ⟨hm.ne_zero⟩)

/-! ### The Weil pairing on `E(Kˢ)[m]` -/

open scoped Classical in
/-- **The Weil pairing on the coefficient module** `E(Kˢ)[m]`, with values in `μ_m`: the Weil
pairing `e_m` of `W` over the separable closure `Kˢ`, for `m` invertible in `K`. -/
def torsionCoeffWeilPairing : W.TorsionCoeff m →+ W.TorsionCoeff m →+ KummerCoeff K m :=
  haveI := neZero_of_isUnit m hm
  let f := (AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm.toAddMonoidHom
  ((Isogeny.weilPairing (W⁄(SeparableClosure K)) m
    hm.natCast_ne_zero_of_algebra).compl₂ f).comp f

open scoped Classical in
/-- `torsionCoeffWeilPairing` is the Weil pairing of `W` over `Kˢ`, read through the identification
`WeierstrassCurve.pointCoeffEquiv` of `E(Kˢ)` with the points of `W⁄Kˢ`. -/
theorem torsionCoeffWeilPairing_apply [NeZero m] (hm' : (m : SeparableClosure K) ≠ 0)
    (P Q : W.TorsionCoeff m) :
    W.torsionCoeffWeilPairing m hm P Q =
      Isogeny.weilPairing (W⁄(SeparableClosure K)) m hm'
        ((AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm P)
        ((AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm Q) :=
  (rfl)

/-- **The Weil pairing is Galois-equivariant** (Silverman III.8.1(e)):
`e_m(σ P, σ Q) = σ (e_m(P, Q))` for every `σ ∈ G_K`. -/
@[simp]
theorem torsionCoeffWeilPairing_smul (σ : AbsoluteGaloisGroup K) (P Q : W.TorsionCoeff m) :
    W.torsionCoeffWeilPairing m hm (σ • P) (σ • Q) = σ • W.torsionCoeffWeilPairing m hm P Q := by
  classical
  have := neZero_of_isUnit m hm
  rw [torsionCoeffWeilPairing_apply _ _ _ hm.natCast_ne_zero_of_algebra,
    torsionCoeffWeilPairing_apply _ _ _ hm.natCast_ne_zero_of_algebra,
    torsionByCongr_pointCoeffEquiv_symm_smul, torsionByCongr_pointCoeffEquiv_symm_smul,
    weilPairing_torsionGaloisAction]
  exact Additive.toMul.injective <| Subtype.ext <| Units.ext <| by
    simp [restrictRootsOfUnity_coe_apply, AlgEquiv.smul_units_def]

/-- **The Weil pairing is nondegenerate**: if `e_m(P, Q) = 1` for every `Q ∈ E(Kˢ)[m]`, then
`P = O`. -/
theorem torsionCoeffWeilPairing_nondegenerate {P : W.TorsionCoeff m}
    (hP : ∀ Q, W.torsionCoeffWeilPairing m hm P Q = 0) : P = 0 := by
  classical
  have := neZero_of_isUnit m hm
  refine (AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm.injective ?_
  rw [map_zero]
  refine Isogeny.weilPairing_nondegenerate _ m hm.natCast_ne_zero_of_algebra
    fun Q ↦ ?_
  simpa [torsionCoeffWeilPairing_apply _ _ _ hm.natCast_ne_zero_of_algebra] using
    hP (AddEquiv.torsionByCongr W.pointCoeffEquiv m Q)

include hm in
/-- If `G_K` fixes every point of `E(Kˢ)[m]`, it fixes every `m`-th root of unity: these are
values of the Weil pairing, which is equivariant. -/
private theorem smul_kummerCoeff_eq_self_of_forall_smul_eq_self
    (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P)
    (σ : AbsoluteGaloisGroup K) (x : KummerCoeff K m) : σ • x = x := by
  classical
  have := neZero_of_isUnit m hm
  have hσ : W.torsionGaloisAction m σ = 1 := by
    refine Multiplicative.toAdd.injective (AddEquiv.ext fun P ↦ ?_)
    have := W.torsionByCongr_pointCoeffEquiv_symm_smul σ
      (AddEquiv.torsionByCongr W.pointCoeffEquiv m P)
    rw [h, AddEquiv.symm_apply_apply] at this
    exact this.symm
  refine Additive.toMul.injective <| Subtype.ext <| Units.ext ?_
  simpa [AlgEquiv.smul_units_def] using
    W.algEquiv_apply_eq_self_of_torsionGaloisAction_eq_one
      hm.natCast_ne_zero_of_algebra hσ
      (ζ := ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K))
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one])

/-! ### Change of field -/

section BaseChange

variable {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

omit [W.IsElliptic] in
/-- The base change of `W` to `Kˢ`, transported along `τ : Kˢ → Lˢ`, is the base change of `W⁄L`
to `Lˢ`. -/
private theorem map_baseChange_separableClosure :
    (W⁄(SeparableClosure K)).map (τ : SeparableClosure K →+* SeparableClosure L) =
      (W⁄L)⁄(SeparableClosure L) :=
  (map_baseChange W τ).trans
    (map_baseChange W (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm

omit [W.IsElliptic] in
open scoped Classical in
/-- The map `E(Kˢ)[m] → E(Lˢ)[m]` induced by `τ` is `WeierstrassCurve.torsionMapAlong`, read
through the identifications of the coefficient modules with the points of the base changes. -/
private theorem torsionByCongr_symm_torsionCoeffBaseChange (P : W.TorsionCoeff m) :
    (AddEquiv.torsionByCongr (W⁄L).pointCoeffEquiv m).symm (W.torsionCoeffBaseChange τ m P) =
      AddEquiv.torsionByCongr
        (AddEquiv.cast (M := fun V : WeierstrassCurve (SeparableClosure L) ↦ V.toAffine.Point)
          (W.map_baseChange_separableClosure τ)) m
        ((W⁄(SeparableClosure K)).torsionMapAlong
          (τ : SeparableClosure K →+* SeparableClosure L) m
          ((AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm P)) := by
  apply Subtype.ext
  obtain ⟨P, hP⟩ := P
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  simp only [AddEquiv.torsionByCongr_symm_apply_coe, AddEquiv.torsionByCongr_apply_coe,
    coe_torsionCoeffBaseChange, coe_torsionMapAlong_apply, AddEquiv.symm_apply_apply]
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, Affine.Point.mapAlong_zero, map_zero,
      map_zero]
  · rw [pointCoeffBaseChange_pointCoeffEquiv_some, AddEquiv.symm_apply_apply,
      Affine.Point.mapAlong_some, AddEquiv.cast_apply,
      Affine.Point.cast_some (W.map_baseChange_separableClosure τ)]
    simp

variable {m}

/-- **The Weil pairing commutes with change of field** (Silverman III.8.1): for an embedding
`τ : Kˢ → Lˢ` over `K`, `e_m(τ P, τ Q) = τ (e_m(P, Q))`. -/
theorem torsionCoeffWeilPairing_torsionCoeffBaseChange (P Q : W.TorsionCoeff m) :
    (W⁄L).torsionCoeffWeilPairing m (by simpa using hm.map (algebraMap K L))
        (W.torsionCoeffBaseChange τ m P) (W.torsionCoeffBaseChange τ m Q) =
      kummerCoeffBaseChange m τ (W.torsionCoeffWeilPairing m hm P Q) := by
  classical
  have := neZero_of_isUnit m hm
  have hm' : (m : SeparableClosure K) ≠ 0 := hm.natCast_ne_zero_of_algebra
  have hmτ : (m : SeparableClosure L) ≠ 0 := hm.natCast_ne_zero_of_algebra
  rw [torsionCoeffWeilPairing_apply _ _ _ hmτ, torsionCoeffWeilPairing_apply _ _ _ hm',
    torsionByCongr_symm_torsionCoeffBaseChange, torsionByCongr_symm_torsionCoeffBaseChange,
    weilPairing_torsionByCongr_cast _ _ hmτ, weilPairing_torsionMapAlong _ _ _ hm']
  exact Additive.toMul.injective <| Subtype.ext <| Units.ext <| by
    simp [restrictRootsOfUnity_coe_apply]

end BaseChange

/-! ### The coefficient map attached to a rational torsion point -/

section Rational

variable [DecidableEq K]

/-- **The map `E(Kˢ)[m] → μ_m` of a rational torsion point**: for `T ∈ E(K)[m]`, the
`G_K`-equivariant map `P ↦ e_m(P, T)`. It is equivariant because the Weil pairing is and `G_K`
fixes `T`. -/
def weilPairingCoeff (T : AddSubgroup.torsionBy W.toAffine.Point m) :
    W.TorsionCoeff m →+[AbsoluteGaloisGroup K] KummerCoeff K m :=
  { (W.torsionCoeffWeilPairing m hm).flip (W.baseTorsionCoeff m T) with
    map_smul' σ P := by
      simp only [AddMonoidHom.toFun_eq_coe, AddMonoidHom.flip_apply, MonoidHom.id_apply]
      rw [← torsionCoeffWeilPairing_smul, smul_baseTorsionCoeff] }

/-- `weilPairingCoeff T` is the Weil pairing with the image of `T` in `E(Kˢ)[m]`. -/
@[simp]
theorem weilPairingCoeff_apply (T : AddSubgroup.torsionBy W.toAffine.Point m)
    (P : W.TorsionCoeff m) :
    W.weilPairingCoeff m hm T P = W.torsionCoeffWeilPairing m hm P (W.baseTorsionCoeff m T) :=
  (rfl)

/-! ### Restriction to a field extension -/

section Restriction

variable {L : Type*} [Field L] [Algebra K L] [DecidableEq L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- **Restriction commutes with the maps `H¹(G, E[m]) → H¹(G, μ_m)`**: for a field extension
`L / K` with an embedding `τ : Kˢ → Lˢ` over `K`, and `T' ∈ E(L)[m]` the image of `T ∈ E(K)[m]`,
restricting to `G_L` and then pairing with `T'` is pairing with `T` and then restricting the roots
of unity along `τ`. -/
theorem explicitMap1_explicitCoeff1_weilPairingCoeff {T : AddSubgroup.torsionBy W.toAffine.Point m}
    {T' : AddSubgroup.torsionBy (W⁄L).toAffine.Point m}
    (hT : (T' : (W⁄L).toAffine.Point) = W.toAffine.pointMap L T)
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange m τ)
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul m τ)
        (explicitCoeff1 _ _ (W.weilPairingCoeff m hm T) continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ ((W⁄L).weilPairingCoeff m (by simpa using hm.map (algebraMap K L)) T')
        continuous_of_discreteTopology (W.torsionRes τ m c) := by
  have hT : W.torsionCoeffBaseChange τ m (W.baseTorsionCoeff m T) =
      (W⁄L).baseTorsionCoeff m T' :=
    Subtype.ext (by simp [hT])
  rw [explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1, torsionRes_eq_explicitMap1]
  refine explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (AddMonoidHom.ext fun P ↦ ?_) c
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, DistribMulActionHom.coe_fn_coe,
    weilPairingCoeff_apply]
  rw [← hT, torsionCoeffWeilPairing_torsionCoeffBaseChange]

end Restriction

/-! ### Detecting classes when `E[m]` is rational -/

/-- **The Weil pairing detects `H¹(G_K, E[m])` when `E[m] ⊆ E(K)`**: if `G_K` fixes every point of
`E(Kˢ)[m]`, then a class of `H¹(G_K, E[m])` is determined by its images in `H¹(G_K, μ_m)` under
the maps `e_m(·, T)` attached to the points `T ∈ E(K)[m]`. Via the Kummer isomorphism
`H¹(G_K, μ_m) ≃ Kˣ ⧸ (Kˣ)ᵐ` this embeds `H¹(G_K, E[m])` into a product of copies of
`Kˣ ⧸ (Kˣ)ᵐ` (Silverman VIII.1 and X.1). -/
theorem explicitCoeff1_weilPairingCoeff_injective
    (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P) :
    Function.Injective fun (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m))
      (T : AddSubgroup.torsionBy W.toAffine.Point m) ↦
        explicitCoeff1 _ _ (W.weilPairingCoeff m hm T) continuous_of_discreteTopology c := by
  let F : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
      (AddSubgroup.torsionBy W.toAffine.Point m → H1 (AbsoluteGaloisGroup K) (KummerCoeff K m)) :=
    AddMonoidHom.pi fun T ↦
      explicitCoeff1 _ _ (W.weilPairingCoeff m hm T) continuous_of_discreteTopology
  refine (injective_iff_map_eq_zero F).2 fun c hc ↦ ?_
  induction c using QuotientAddGroup.induction_on with
  | _ z =>
  rw [H1pi_eq_zero_iff]
  -- `z` vanishes identically: each value is killed by `e_m(·, Q)` for every `Q ∈ E(Kˢ)[m]`
  suffices hz : (z : AbsoluteGaloisGroup K → W.TorsionCoeff m) = 0 by
    rw [hz]
    exact zero_mem _
  refine funext fun g ↦ W.torsionCoeffWeilPairing_nondegenerate m hm fun Q ↦ ?_
  -- `Q` is fixed by `G_K`, so it is the image of a point `T ∈ E(K)[m]`
  obtain ⟨T, rfl⟩ := W.exists_baseTorsionCoeff_eq_of_forall_smul_eq fun σ ↦ h σ Q
  -- the image of `z` under `e_m(·, T)` is a coboundary, and `G_K` acts trivially on `μ_m`
  have hcT : explicitCoeff1 _ _ (W.weilPairingCoeff m hm T) continuous_of_discreteTopology
      (z : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) = 0 := congrFun hc T
  rw [explicitCoeff1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hcT
  obtain ⟨a, ha⟩ := hcT
  have hg := (cocyclesMap1_apply _ _ _ _ _ _ _ _ z g).symm.trans (ha g).symm
  rw [smul_kummerCoeff_eq_self_of_forall_smul_eq_self W m hm h, sub_self] at hg
  simpa using hg

/-- **Finiteness through the Weil pairing**: if `G_K` fixes every point of `E(Kˢ)[m]`, a set of
classes of `H¹(G_K, E[m])` is finite as soon as, for each `T ∈ E(K)[m]`, its image in
`H¹(G_K, μ_m)` under `e_m(·, T)` is finite. -/
theorem finite_of_forall_finite_image_explicitCoeff1_weilPairingCoeff
    (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P)
    {A : Set (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m))}
    (hA : ∀ T : AddSubgroup.torsionBy W.toAffine.Point m,
      (explicitCoeff1 _ _ (W.weilPairingCoeff m hm T) continuous_of_discreteTopology ''
        A).Finite) :
    A.Finite := by
  have : Finite (AddSubgroup.torsionBy W.toAffine.Point m) :=
    W.finite_torsionBy (Int.natCast_ne_zero.2 (neZero_of_isUnit m hm).ne)
  refine ((Set.Finite.pi hA).preimage
    (W.explicitCoeff1_weilPairingCoeff_injective m hm h).injOn).subset fun c hc ↦ ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
  exact fun T ↦ Set.mem_image_of_mem _ hc

end Rational

end WeierstrassCurve
