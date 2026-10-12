/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.EquivariantKummer
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteQuotient
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.Tensor

/-!
# Equivariant Kummer theory on a finite Galois quotient of `G_F`

Let `F` be a field, `n` a natural number invertible in `F`, `G_F = Field.absoluteGaloisGroup F`,
and `V` an open normal subgroup of `G_F`. Let `L/F` be a finite normal extension embedded in the
separable closure by `σ : L →ₐ[F] Fˢ` so that the image of `G_L` in `G_F` along `σ` is `V`
(`(absoluteGaloisGroupExtend F L σ).range = V`), and suppose that `V` acts trivially on `μₙ`, which
is then the inflation of a representation `M` of `G = G_F ⧸ V`
(`exists_fdGalRepOfQuotient_iso_muNRep`). This file proves equivariant Kummer theory in the form
in which the local Euler characteristic computes with it:

```text
kummerH1ConjRepresentationEquiv σ hn hV e : H¹(V, ℤ/n) ≅ M^∨ ⊗ Lˣ ⧸ (Lˣ)ⁿ
```

as `ZMod n`-representations of `G`. Here `G` acts on `H¹(V, ℤ/n)` by conjugation, which is the
representation `h1ConjRepresentation` of the `H¹`-tensor comparison, on `M^∨ = Hom(M, ℤ/n)`
dually, and on the power classes of `L` through `G ≃* Gal(L/F)`
(`TauCeti.absoluteGaloisGroupExtendQuotientEquiv`).
The representation `M` is the same datum as in the computation of `H²` by duality
(`finrank_continuousCohomology_two_fdGalRepOfQuotient`), so `H¹(V, ℤ/n) ≅ μₙ^{-1} ⊗ Lˣ ⧸ (Lˣ)ⁿ`
as representations of `G`, natural in the `F`-automorphisms of `L`.

The equivariant Kummer isomorphism `kummerH1FiniteRepresentationEquiv` is stated on Tau Ceti's
separable-closure model `AbsoluteGaloisGroup F` of the absolute Galois group, for the subgroup
fixing `σ(L)`. The restriction isomorphism `absoluteGaloisGroupRestrictEquiv` carries `V` onto
that subgroup (`TauCeti.absoluteGaloisGroupRestrictSubgroupEquiv`) and identifies the two first
cohomology groups compatibly with conjugation (`restrictSubgroupH1Equiv`,
`restrictSubgroupH1Equiv_smul`). Along
this identification the cyclotomic twist of the Kummer isomorphism with trivial coefficients
(`nsmul_smul_fixingSubgroupKummerEquivOfTrivial`) is the character of `G` on `M`, and the rank-one
twist removal `Representation.rankOneTwistEquiv` gives the equivalence.

## Main definitions

* `TauCeti.ClassFieldTheory.restrictSubgroupH1Equiv`: the induced identification of `H¹` with
  `ℤ/n` coefficients.
* `TauCeti.ClassFieldTheory.kummerH1ConjRepresentationEquiv`: equivariant Kummer theory,
  `H¹(V, ℤ/n) ≅ M^∨ ⊗ Lˣ ⧸ (Lˣ)ⁿ` as representations of `G_F ⧸ V`.

## Main results

* `TauCeti.ClassFieldTheory.restrictSubgroupH1Equiv_smul`: the identification of `H¹` intertwines
  the two conjugation actions.
* `TauCeti.ClassFieldTheory.smul_kummerCoeff_eq_self_of_mem_fixingSubgroup`: if `M` inflates to
  `μₙ`, the subgroup fixing `σ(L)` acts trivially on `μₙ`.
* `TauCeti.ClassFieldTheory.dualTensorHom_kummerH1ConjRepresentationEquiv`: the Kummer class of
  `x` corresponds to `m ↦ log(m) • x`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

attribute [local instance] trivialZModAction

/-- `ZMod n`, with the discrete topology and the trivial action, is a continuous module. -/
local instance {n : ℕ} {H : Type*} [Monoid H] [TopologicalSpace H] :
    ContinuousSMul H (ZMod n) := ⟨continuous_snd⟩

variable {F : Type} [Field F] {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L]
  (σ : L →ₐ[F] SeparableClosure F) {V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)}

/-! ### `H¹(G_L, ℤ/n)` in the two models of `G_F` -/

variable (n : ℕ)

/-- **`H¹(G_L, ℤ/n)` in the two models of `G_F`**: pullback along
`absoluteGaloisGroupRestrictSubgroupEquiv` identifies the first cohomology, with trivial
coefficients `ℤ/n`, of the subgroup of `Gal(Fˢ/F)` fixing `σ(L)` with that of `V`. -/
def restrictSubgroupH1Equiv (hV : (absoluteGaloisGroupExtend F L σ).range = V.toSubgroup) :
    H1 σ.fieldRange.fixingSubgroup (ZMod n) ≃+ H1 V.toSubgroup (ZMod n) :=
  explicitMap1Equiv _ _ _ _ (absoluteGaloisGroupRestrictSubgroupEquiv F L σ hV) (AddEquiv.refl _)
    continuous_of_discreteTopology continuous_of_discreteTopology fun _ _ ↦ rfl

/-- `restrictSubgroupH1Equiv` is the pullback along `absoluteGaloisGroupRestrictSubgroupEquiv`. -/
theorem restrictSubgroupH1Equiv_apply
    (hV : (absoluteGaloisGroupExtend F L σ).range = V.toSubgroup)
    (x : H1 σ.fieldRange.fixingSubgroup (ZMod n)) :
    restrictSubgroupH1Equiv σ n hV x =
      explicitMap1 _ _ _ _ (absoluteGaloisGroupRestrictSubgroupEquiv F L σ hV)
        (AddMonoidHom.id (ZMod n)) continuous_id (fun _ _ ↦ rfl) x :=
  explicitMap1Equiv_apply _ _ _ _ _ _ _ _ _ x

variable [Normal F L]

/-- **The identification of `H¹` is Galois equivariant**: it intertwines conjugation by the image
of `g ∈ G_F` in `Gal(Fˢ/F)` on the cohomology of the subgroup fixing `σ(L)` with conjugation by `g`
on the cohomology of `V`. -/
theorem restrictSubgroupH1Equiv_smul
    (hV : (absoluteGaloisGroupExtend F L σ).range = V.toSubgroup)
    (g : Field.absoluteGaloisGroup F) (x : H1 σ.fieldRange.fixingSubgroup (ZMod n)) :
    restrictSubgroupH1Equiv σ n hV (absoluteGaloisGroupRestrictEquiv F g • x) =
      g • restrictSubgroupH1Equiv σ n hV x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    -- Write both conjugations as pullbacks (`smul_mk`), so each side is a composite of two
    -- `explicitMap1`s applied to the class of `c`.
    rw [restrictSubgroupH1Equiv_apply, restrictSubgroupH1Equiv_apply, explicitMap1_mk, smul_mk,
      smul_mk, ← explicitMap1_mk, ← explicitMap1_mk, ← explicitMap1_mk]
    -- The composites of the group homomorphisms agree because the restriction isomorphism is a
    -- homomorphism; those of the coefficient maps because the action on `ℤ/n` is trivial
    -- (`trivialZModAction`).
    exact explicitMap1_explicitMap1_of_comp_eq
      (hφ := ContinuousMonoidHom.ext fun _ ↦ Subtype.ext (by simp))
      (hqf := AddMonoidHom.ext fun _ ↦ rfl) ..

/-! ### The roots of unity as a representation of the quotient -/

variable {n}

/-- The isomorphism `e` read on `galRepOfQuotient`, whose underlying module is that of `M`. -/
private def inflationIso {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) :
    (galRepOfQuotient n F V).obj ((forget₂ (FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸
      V.toSubgroup)) (Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))).obj M) ≅
        muNRep n F :=
  eqToIso (fdGalRepOfQuotient_obj n F V M).symm ≪≫ e

/-- The coordinate `M ≃ μₙ ≃ ℤ/n` on a representation `M` inflating to `μₙ`, through the chosen
identification `kummerCoeffAddEquivZMod`. -/
private def coordinate (hn : IsUnit (n : F))
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) : M ≃ₗ[ZMod n] ZMod n :=
  (({ toFun := fun x ↦ (inflationIso e).hom.hom x
      invFun := fun x ↦ (inflationIso e).inv.hom x
      left_inv := (inflationIso e).hom_inv_id_apply
      right_inv := (inflationIso e).inv_hom_id_apply
      map_add' := map_add (inflationIso e).hom.hom } : M ≃+ (muNRep n F).V).trans
    ((kummerCoeffEquivMuNRep n F).symm.trans (kummerCoeffAddEquivZMod hn))).toLinearEquiv
    (ZMod.map_smul _)

/-- `coordinate` is `e` followed by the coefficient dictionary and `kummerCoeffAddEquivZMod`. -/
private theorem coordinate_apply (hn : IsUnit (n : F))
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) (m : M) :
    coordinate hn e m =
      kummerCoeffAddEquivZMod hn ((kummerCoeffEquivMuNRep n F).symm ((inflationIso e).hom.hom m)) :=
  (rfl)

/-- The inverse of `coordinate`. -/
private theorem coordinate_symm_apply (hn : IsUnit (n : F))
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) (z : ZMod n) :
    (coordinate hn e).symm z =
      (inflationIso e).inv.hom (kummerCoeffEquivMuNRep n F ((kummerCoeffAddEquivZMod hn).symm z)) :=
  (rfl)

/-- If `M` inflates to `μₙ`, then the image of `g` in `Gal(Fˢ/F)` acts on `μₙ` as the class of
`g` acts on `M`, read through `coordinate`. -/
private theorem smul_kummerCoeff_eq (hn : IsUnit (n : F))
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) (g : Field.absoluteGaloisGroup F)
    (ξ : KummerCoeff F n) :
    absoluteGaloisGroupRestrictEquiv F g • ξ =
      (kummerCoeffAddEquivZMod hn).symm (coordinate hn e
        (M.ρ (g : Field.absoluteGaloisGroup F ⧸ V.toSubgroup)
          ((coordinate hn e).symm (kummerCoeffAddEquivZMod hn ξ)))) := by
  apply (kummerCoeffEquivMuNRep n F).injective
  simp only [kummerCoeffEquivMuNRep_smul, coordinate_apply, coordinate_symm_apply,
    AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  conv_lhs => rw [← (inflationIso e).inv_hom_id_apply (kummerCoeffEquivMuNRep n F ξ)]
  rw [← TopRep.hom_comm_apply]
  -- The inflated action is that of the class of `g` on the underlying representation of `M`.
  exact congrArg (inflationIso e).hom.hom ((galRepOfQuotient_ρ_apply n F V _ g _).trans
    (LinearMap.congr_fun (DFunLike.congr_fun (FDRep.forget₂_ρ M) _) _))

omit [Normal F L] in
/-- If `M` inflates to `μₙ`, the subgroup of `Gal(Fˢ/F)` fixing `σ(L)` acts trivially on `μₙ`. -/
theorem smul_kummerCoeff_eq_self_of_mem_fixingSubgroup (hn : IsUnit (n : F))
    (hV : (absoluteGaloisGroupExtend F L σ).range = V.toSubgroup)
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) (h : AbsoluteGaloisGroup F)
    (hh : h ∈ σ.fieldRange.fixingSubgroup) (ξ : KummerCoeff F n) : h • ξ = ξ := by
  rw [← map_range_absoluteGaloisGroupExtend F L σ, hV, Subgroup.mem_map] at hh
  obtain ⟨g, hg, rfl⟩ := hh
  rw [MonoidHom.coe_ofClass, smul_kummerCoeff_eq hn e, (QuotientGroup.eq_one_iff g).2 hg, map_one,
    Module.End.one_apply, LinearEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

/-! ### Equivariant Kummer theory -/

/-- **Equivariant Kummer theory on a finite Galois quotient of `G_F`.** Let `n` be invertible in
`F`, let the image of `G_L` in `G_F` along `σ` be the open normal subgroup `V`, and let `M` be a
representation of `G = G_F ⧸ V` inflating to `μₙ` (`e`). Then `H¹(V, ℤ/n)` is isomorphic to
`M^∨ ⊗ Lˣ ⧸ (Lˣ)ⁿ` as a `ZMod n`-representation of `G`, where `G` acts on `H¹(V, ℤ/n)` by
conjugation (`h1ConjRepresentation`) and on the power classes of `L` through
`absoluteGaloisGroupExtendQuotientEquiv F L σ hV : G ≃* Gal(L/F)`. That is,
`H¹(L, ℤ/n) ≅ μₙ^{-1} ⊗ Lˣ ⧸ (Lˣ)ⁿ`, naturally in the `F`-automorphisms of `L`.

It sends the Kummer class of `x` to `m ↦ log(m) • x`
(`dualTensorHom_kummerH1ConjRepresentationEquiv`). -/
def kummerH1ConjRepresentationEquiv (hn : IsUnit (n : F))
    (hV : (absoluteGaloisGroupExtend F L σ).range = V.toSubgroup)
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F) :
    (h1ConjRepresentation (p := n) (G := Field.absoluteGaloisGroup F) (N := V.toSubgroup)).Equiv
      ((Representation.dual M.ρ).tprod ((powerClassRepresentation (K := F) (L := L) n).comp
        (absoluteGaloisGroupExtendQuotientEquiv F L σ hV).toMonoidHom)) :=
  Representation.rankOneTwistEquiv M.ρ _ _ (coordinate hn e)
    (((fixingSubgroupKummerEquivOfTrivial σ hn (kummerCoeffAddEquivZMod hn) (fun _ _ ↦ rfl)
      (smul_kummerCoeff_eq_self_of_mem_fixingSubgroup σ hn hV e)).trans
        (restrictSubgroupH1Equiv σ n hV)).toLinearEquiv (ZMod.map_smul _))
    fun q x ↦ by
      have : NeZero n := ⟨by rintro rfl; simp at hn⟩
      induction q using QuotientGroup.induction_on with | H g => ?_
      -- `g` acts on `μₙ` as the `c`th power map, for `c` the character of `M` at `g`.
      generalize hc : Representation.rankOneCharacter M.ρ (coordinate hn e)
        (g : Field.absoluteGaloisGroup F ⧸ V.toSubgroup) = c
      have hk (ξ : KummerCoeff F n) : absoluteGaloisGroupRestrictEquiv F g • ξ = c.val • ξ := by
        rw [smul_kummerCoeff_eq hn e, Representation.rankOneCharacter_smul M.ρ (coordinate hn e),
          hc, map_smul, LinearEquiv.apply_symm_apply, ZMod.map_smul, AddEquiv.symm_apply_apply,
          ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]
      rw [h1ConjRepresentation_quotient_mk_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        absoluteGaloisGroupExtendQuotientEquiv_mk, powerClassRepresentation_apply,
        AddEquiv.coe_toLinearEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
        explicitConj1_apply_eq_smul]
      -- The twisted equivariance reads the automorphism of `L` through `L →ₐ[F] L`.
      have hmap : ((σ.restrictNormalHom (absoluteGaloisGroupRestrictEquiv F g) : L →ₐ[F] L) :
          L →* L) = σ.restrictNormalHom (absoluteGaloisGroupRestrictEquiv F g) :=
        MonoidHom.ext fun _ ↦ rfl
      rw [← hmap, ← nsmul_smul_fixingSubgroupKummerEquivOfTrivial σ hn _ _ _
        (absoluteGaloisGroupRestrictEquiv F g) _
        (σ.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv F g)) c.val hk x,
        map_nsmul, restrictSubgroupH1Equiv_smul, ← Nat.cast_smul_eq_nsmul (ZMod n),
        ZMod.natCast_zmod_val]

/-- **The equivariant Kummer isomorphism on Kummer classes.** Under
`kummerH1ConjRepresentationEquiv`, the Kummer class of a power class `x`, read on `V` through
`restrictSubgroupH1Equiv`, corresponds to the homomorphism `M → Lˣ ⧸ (Lˣ)ⁿ` sending `m` to
`log(m) • x`, where `log : M ≃ μₙ ≃ ℤ/n` is `e` followed by `kummerCoeffAddEquivZMod`. -/
@[simp]
theorem dualTensorHom_kummerH1ConjRepresentationEquiv (hn : IsUnit (n : F))
    (hV : (absoluteGaloisGroupExtend F L σ).range = V.toSubgroup)
    {M : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)}
    (e : (fdGalRepOfQuotient n F V).obj M ≅ muNRep n F)
    (x : Additive (powerClassQuotient Lˣ n)) (m : M) :
    dualTensorHom (ZMod n) M (Additive (powerClassQuotient Lˣ n))
        (kummerH1ConjRepresentationEquiv σ hn hV e (restrictSubgroupH1Equiv σ n hV
          (fixingSubgroupKummerEquivOfTrivial σ hn (kummerCoeffAddEquivZMod hn) (fun _ _ ↦ rfl)
            (smul_kummerCoeff_eq_self_of_mem_fixingSubgroup σ hn hV e) x))) m =
      kummerCoeffAddEquivZMod hn ((kummerCoeffEquivMuNRep n F).symm
        ((eqToIso (fdGalRepOfQuotient_obj n F V M).symm ≪≫ e).hom.hom m)) • x := by
  rw [kummerH1ConjRepresentationEquiv, Representation.dualTensorHom_rankOneTwistEquiv,
    LinearEquiv.rankOneHomEquiv_apply_apply]
  simp [coordinate_apply, inflationIso]

end TauCeti.ClassFieldTheory
