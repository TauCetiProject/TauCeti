/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic

import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.KernelWeilPairing
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
import TauCeti.Topology.Algebra.GroupAction.InternalHom.DoubleDual

/-!
# The Weil pairing of an isogeny on Galois coefficient modules

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, of degree `n` invertible in
`K`, with dual `φ̂ : W₂ → W₁`. Its kernels over a separable closure `Kˢ` are the discrete
`G_K`-modules `E₁(Kˢ)[φ]` and `E₂(Kˢ)[φ̂]` (`TauCeti.Isogeny.Hom.KerCoeff`), and the Weil pairing
`e_n` of `W₁` induces the **isogeny Weil pairing**

`e_φ : E₁(Kˢ)[φ] × E₂(Kˢ)[φ̂] → μ_n`,

characterized by `e_φ(P, φ R) = e_n(P, R)` for `R ∈ E₁(Kˢ)[n]`. Every point of `E₂(Kˢ)[φ̂]` is of
the form `φ R` (`TauCeti.Isogeny.torsionCoeffToDualKerCoeff_surjective`), and the value does not
depend on the choice of `R` because `E₁(Kˢ)[φ]` is isotropic for `e_n`. The pairing is
`G_K`-equivariant and nondegenerate on both sides, so it identifies `E₂(Kˢ)[φ̂]` with the internal
dual `Hom(E₁(Kˢ)[φ], μ_n)` as discrete Galois modules (convention `Q ↦ (P ↦ e_φ(P, Q))`). In
particular the two kernels have the same order.

The resulting cup product pairs `H¹(K, E₁[φ])` with `H¹(K, E₂[φ̂])` into `H²(K, μ_n)`; on cocycles
it is `(g, h) ↦ e_φ(a(g), g • b(h))`. This is the pairing under which the local conditions of the
Selmer groups `Sel_φ` and `Sel_φ̂` are compared in Cassels' proof of the isogeny invariance of the
Birch–Swinnerton-Dyer quotient; local Tate duality for it is
`TauCeti.Isogeny.localTateKerWeilPairing_bijective`.

## Main definitions

* `TauCeti.Isogeny.kerCoeffWeilPairing`: the pairing `e_φ : E₁(Kˢ)[φ] × E₂(Kˢ)[φ̂] → μ_n`.
* `TauCeti.Isogeny.kerCoeffWeilDual`: the equivariant map `E₂(Kˢ)[φ̂] → Hom(E₁(Kˢ)[φ], μ_n)`.
* `TauCeti.Isogeny.kerH1WeilPairing`: the cup product
  `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → H²(K, μ_n)` along `e_φ`.

## Main results

* `TauCeti.Isogeny.torsionCoeffWeilPairing_eq_zero_of_pointCoeffMap_eq_zero`: `E₁(Kˢ)[φ]` is
  isotropic for `e_n`.
* `TauCeti.Isogeny.kerCoeffWeilPairing_torsionCoeffToDualKerCoeff`: `e_φ(P, φ R) = e_n(P, R)`, and
  `TauCeti.Isogeny.kerCoeffWeilPairing_unique`: this determines `e_φ`.
* `TauCeti.Isogeny.kerCoeffWeilPairing_smul`: `e_φ` is Galois-equivariant.
* `TauCeti.Isogeny.kerCoeffWeilPairing_nondegenerate_left` and
  `TauCeti.Isogeny.kerCoeffWeilPairing_nondegenerate_right`: `e_φ` is nondegenerate.
* `TauCeti.Isogeny.natCard_kerCoeff_dual`: `E₂(Kˢ)[φ̂]` and `E₁(Kˢ)[φ]` have the same order.
* `TauCeti.Isogeny.kerCoeffWeilDual_bijective`: `E₂(Kˢ)[φ̂] ≅ Hom(E₁(Kˢ)[φ], μ_n)`.
* `TauCeti.Isogeny.kerH1WeilPairing_eq_explicitCup11`: the cup product on cocycles.

## Implementation notes

Over a separably closed field the corresponding pairing on points is
`TauCeti.Isogeny.kerWeilPairing`. Only its isotropy input is transported to `Kˢ`; the coefficient
pairing is constructed directly from `WeierstrassCurve.torsionCoeffWeilPairing`, which supplies its
Galois equivariance. Nondegeneracy in the second argument is obtained by counting: nondegeneracy in
the first argument, for `φ` and for `φ̂`, bounds the order of each kernel by that of the other.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2.
-/

public section

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology

namespace TauCeti.Isogeny

open Hom

/-- The kernel of an isogeny over a separably closed field is isotropic for the Weil pairing at
any `N` equal to its degree. This is `TauCeti.Isogeny.weilPairing_eq_zero_of_pointMap_eq_zero`
with the degree generalised, for use after a base change, which changes the degree only up to
propositional equality. -/
private theorem weilPairing_eq_zero_of_degree_eq {F : Type*} [Field F] [DecidableEq F]
    [IsSepClosed F] {V₁ V₂ : WeierstrassCurve.Affine F} [V₁.IsElliptic] [V₂.IsElliptic]
    (ψ : Isogeny V₁ V₂) {N : ℕ} [NeZero N] (hN : ψ.degree = N) (hd : (N : F) ≠ 0)
    {P R : Submodule.torsionBy ℤ V₁.Point (N : ℤ)}
    (hP : (Hom.ofIsogeny ψ).pointMap P = 0) (hR : (Hom.ofIsogeny ψ).pointMap R = 0) :
    weilPairing V₁ N hd P R = 0 := by
  subst hN
  exact ψ.weilPairing_eq_zero_of_pointMap_eq_zero hd hP hR

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-! ### Isotropy of the kernel -/

variable (hn : IsUnit (φ.degree : K))

include hn in
/-- **The kernel of an isogeny is isotropic for the Weil pairing at its degree**: if
`φ P = φ R = 0` for `P, R ∈ E₁(Kˢ)[n]`, `n = deg φ`, then `e_n(P, R) = 0`. -/
theorem torsionCoeffWeilPairing_eq_zero_of_pointCoeffMap_eq_zero
    {P R : W₁.TorsionCoeff φ.degree}
    (hP : (ofIsogeny φ).pointCoeffMap P = 0) (hR : (ofIsogeny φ).pointCoeffMap R = 0) :
    W₁.torsionCoeffWeilPairing φ.degree hn P R = 0 := by
  classical
  have hd : (φ.degree : SeparableClosure K) ≠ 0 := hn.natCast_ne_zero_of_algebra
  rw [W₁.torsionCoeffWeilPairing_apply _ hn hd]
  -- Over `Kˢ`, a point of `E₁(Kˢ)[φ]` is killed by the base change of `φ`.
  have key (Q : W₁.TorsionCoeff φ.degree) (hQ : (ofIsogeny φ).pointCoeffMap Q = 0) :
      (ofIsogeny (φ.map (algebraMap K (SeparableClosure K)))).pointMap
        ((AddEquiv.torsionByCongr W₁.pointCoeffEquiv φ.degree).symm Q :
          (W₁⁄(SeparableClosure K)).toAffine.Point) = 0 := by
    have h := congrArg W₂.pointCoeffEquiv.symm hQ
    rw [pointCoeffEquiv_symm_pointCoeffMap, map_zero] at h
    rw [AddEquiv.torsionByCongr_symm_apply_coe]
    exact (congrArg (fun g ↦ g.pointMap (W₁.pointCoeffEquiv.symm (Q : W₁.PointCoeff)))
      (ofIsogeny_map φ _)).symm.trans h
  exact weilPairing_eq_zero_of_degree_eq _ (degree_map φ _) hd (key P hP) (key R hR)

/-! ### The isogeny Weil pairing -/

/-- **The isogeny Weil pairing on the Galois coefficient modules**, the pairing
`e_φ : E₁(Kˢ)[φ] × E₂(Kˢ)[φ̂] → μ_n` for `n = deg φ` invertible in `K`. It is characterized by
`e_φ(P, φ R) = e_n(P, R)` for `R ∈ E₁(Kˢ)[n]`
(`TauCeti.Isogeny.kerCoeffWeilPairing_torsionCoeffToDualKerCoeff`). -/
def kerCoeffWeilPairing : (ofIsogeny φ).KerCoeff →+ (ofIsogeny φ.dual).KerCoeff →+
    KummerCoeff K φ.degree := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  let ψ : W₁.TorsionCoeff φ.degree →+ (ofIsogeny φ.dual).KerCoeff := φ.torsionCoeffToDualKerCoeff
  let pairing := (W₁.torsionCoeffWeilPairing φ.degree hn).comp
    (φ.kerCoeffToTorsionCoeff : (ofIsogeny φ).KerCoeff →+ W₁.TorsionCoeff φ.degree)
  have vanishing (P : (ofIsogeny φ).KerCoeff) : ψ.ker ≤ (pairing P).ker := fun R hR ↦
    φ.torsionCoeffWeilPairing_eq_zero_of_pointCoeffMap_eq_zero hn
      (by
        have hP : (ofIsogeny φ).pointCoeffMap (P : W₁.PointCoeff) = 0 := P.2
        simpa using hP)
      (by simpa [ψ, Subtype.ext_iff] using hR)
  let lift := ψ.liftOfSurjective (G₃ := KummerCoeff K φ.degree)
    φ.torsionCoeffToDualKerCoeff_surjective
  refine { toFun := fun P ↦ lift ⟨pairing P, vanishing P⟩
           map_zero' := ?_
           map_add' := ?_ }
  · refine AddMonoidHom.ext fun Q ↦ ?_
    obtain ⟨R, rfl⟩ : ∃ R, ψ R = Q := φ.torsionCoeffToDualKerCoeff_surjective Q
    simp only [lift, AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      map_zero, AddMonoidHom.zero_apply]
  · intro P P'
    refine AddMonoidHom.ext fun Q ↦ ?_
    obtain ⟨R, rfl⟩ : ∃ R, ψ R = Q := φ.torsionCoeffToDualKerCoeff_surjective Q
    simp only [lift, AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      _root_.map_add, AddMonoidHom.add_apply]

/-- **The characteristic formula of the isogeny Weil pairing**: `e_φ(P, φ R) = e_n(P, R)` for
`P ∈ E₁(Kˢ)[φ]` and `R ∈ E₁(Kˢ)[n]`, `n = deg φ`. -/
@[simp]
theorem kerCoeffWeilPairing_torsionCoeffToDualKerCoeff (P : (ofIsogeny φ).KerCoeff)
    (R : W₁.TorsionCoeff φ.degree) :
    φ.kerCoeffWeilPairing hn P (φ.torsionCoeffToDualKerCoeff R) =
      W₁.torsionCoeffWeilPairing φ.degree hn (φ.kerCoeffToTorsionCoeff P) R := by
  simp only [kerCoeffWeilPairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidHom.liftOfSurjective]
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ R

/-- The characteristic formula determines the isogeny Weil pairing. -/
theorem kerCoeffWeilPairing_unique
    (e : (ofIsogeny φ).KerCoeff →+ (ofIsogeny φ.dual).KerCoeff →+ KummerCoeff K φ.degree)
    (he : ∀ P R, e P (φ.torsionCoeffToDualKerCoeff R) =
      W₁.torsionCoeffWeilPairing φ.degree hn (φ.kerCoeffToTorsionCoeff P) R) :
    e = φ.kerCoeffWeilPairing hn := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  refine AddMonoidHom.ext fun P ↦ AddMonoidHom.ext fun Q ↦ ?_
  obtain ⟨R, rfl⟩ := φ.torsionCoeffToDualKerCoeff_surjective Q
  exact (he P R).trans (φ.kerCoeffWeilPairing_torsionCoeffToDualKerCoeff hn P R).symm

/-- **The isogeny Weil pairing is Galois-equivariant**: `e_φ(σ P, σ Q) = σ (e_φ(P, Q))` for every
`σ ∈ G_K`. -/
@[simp]
theorem kerCoeffWeilPairing_smul (σ : AbsoluteGaloisGroup K) (P : (ofIsogeny φ).KerCoeff)
    (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.kerCoeffWeilPairing hn (σ • P) (σ • Q) = σ • φ.kerCoeffWeilPairing hn P Q := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  obtain ⟨R, rfl⟩ := φ.torsionCoeffToDualKerCoeff_surjective Q
  rw [← map_smul φ.torsionCoeffToDualKerCoeff, kerCoeffWeilPairing_torsionCoeffToDualKerCoeff,
    kerCoeffWeilPairing_torsionCoeffToDualKerCoeff, map_smul φ.kerCoeffToTorsionCoeff,
    torsionCoeffWeilPairing_smul]

/-- **The isogeny Weil pairing is nondegenerate in its first argument**: if `e_φ(P, Q) = 0` for
every `Q ∈ E₂(Kˢ)[φ̂]`, then `P = 0`. -/
theorem kerCoeffWeilPairing_nondegenerate_left {P : (ofIsogeny φ).KerCoeff}
    (hP : ∀ Q, φ.kerCoeffWeilPairing hn P Q = 0) : P = 0 := by
  have h := W₁.torsionCoeffWeilPairing_nondegenerate φ.degree hn fun R ↦
    (φ.kerCoeffWeilPairing_torsionCoeffToDualKerCoeff hn P R).symm.trans (hP _)
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

/-- The isogeny Weil pairing, curried, is injective. -/
private theorem kerCoeffWeilPairing_injective : Function.Injective (φ.kerCoeffWeilPairing hn) :=
  (injective_iff_map_eq_zero _).2 fun _ hP ↦
    φ.kerCoeffWeilPairing_nondegenerate_left hn fun Q ↦ by rw [hP, AddMonoidHom.zero_apply]

include hn in
/-- `E₁(Kˢ)[φ]` is at most as large as `E₂(Kˢ)[φ̂]`: it embeds into the characters of
`E₂(Kˢ)[φ̂]` with values in `μ_n`, which are as many as the points of `E₂(Kˢ)[φ̂]`. -/
private theorem natCard_kerCoeff_le_natCard_kerCoeff_dual :
    Nat.card (ofIsogeny φ).KerCoeff ≤ Nat.card (ofIsogeny φ.dual).KerCoeff := by
  have := hn.neZero_natCast
  have : Finite (KummerCoeff K φ.degree) :=
    Finite.of_equiv _ (kummerCoeffAddEquivZMod hn).symm.toEquiv
  have : Finite ((ofIsogeny φ.dual).KerCoeff →+ KummerCoeff K φ.degree) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine (Nat.card_le_card_of_injective _ (φ.kerCoeffWeilPairing_injective hn)).trans_eq ?_
  refine (kummerCoeffAddEquivZMod hn).natCard_addMonoidHom_zmod fun Q ↦ ?_
  simpa [degree_dual] using φ.dual.degree_nsmul_kerCoeff_eq_zero Q

include hn in
/-- **The kernels of an isogeny and of its dual have the same order** over `Kˢ`, for a degree
invertible in `K`. -/
theorem natCard_kerCoeff_dual :
    Nat.card (ofIsogeny φ.dual).KerCoeff = Nat.card (ofIsogeny φ).KerCoeff := by
  have h := φ.dual.natCard_kerCoeff_le_natCard_kerCoeff_dual (by rwa [degree_dual])
  rw [dual_dual] at h
  exact h.antisymm (φ.natCard_kerCoeff_le_natCard_kerCoeff_dual hn)

/-- **The isogeny Weil pairing is nondegenerate in its second argument**: if `e_φ(P, Q) = 0` for
every `P ∈ E₁(Kˢ)[φ]`, then `Q = 0`. -/
theorem kerCoeffWeilPairing_nondegenerate_right {Q : (ofIsogeny φ.dual).KerCoeff}
    (hQ : ∀ P, φ.kerCoeffWeilPairing hn P Q = 0) : Q = 0 := by
  have := hn.neZero_natCast
  have : Finite (KummerCoeff K φ.degree) :=
    Finite.of_equiv _ (kummerCoeffAddEquivZMod hn).symm.toEquiv
  have : Finite ((ofIsogeny φ.dual).KerCoeff →+ KummerCoeff K φ.degree) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hkill (Q' : (ofIsogeny φ.dual).KerCoeff) : φ.degree • Q' = 0 := by
    simpa [degree_dual] using φ.dual.degree_nsmul_kerCoeff_eq_zero Q'
  -- By counting, every character of `E₂(Kˢ)[φ̂]` is `e_φ(P, -)` for some `P`; characters separate
  -- the points of `E₂(Kˢ)[φ̂]`.
  have hsurj : Function.Surjective (φ.kerCoeffWeilPairing hn) :=
    ((φ.kerCoeffWeilPairing_injective hn).bijective_of_nat_card_le (by
      rw [(kummerCoeffAddEquivZMod hn).natCard_addMonoidHom_zmod hkill,
        φ.natCard_kerCoeff_dual hn])).2
  by_contra hne
  obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero hkill hne
  obtain ⟨P, hP⟩ := hsurj ((kummerCoeffAddEquivZMod hn).symm.toAddMonoidHom.comp f)
  refine hf ((kummerCoeffAddEquivZMod hn).symm.map_eq_zero_iff.1 ?_)
  rw [← hQ P, hP, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]

/-! ### Duality of the kernels as Galois modules -/

/-- The isogeny Weil pairing identifies a point `Q ∈ E₂(Kˢ)[φ̂]` with the character
`P ↦ e_φ(P, Q)` of `E₁(Kˢ)[φ]`. The internal hom carries the conjugation action, so this is an
equivariant map even when `Q` is not rational. -/
def kerCoeffWeilDual : (ofIsogeny φ.dual).KerCoeff →+[AbsoluteGaloisGroup K]
    InternalHom (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (KummerCoeff K φ.degree) where
  toFun Q := InternalHom.of _ ((φ.kerCoeffWeilPairing hn).flip Q)
  map_zero' := by simp
  map_add' Q Q' := by simp
  map_smul' g Q := by
    apply InternalHom.ext
    apply AddMonoidHom.ext
    intro P
    simp only [InternalHom.toAddMonoidHom_smul, homAction_apply, AddMonoidHom.flip_apply]
    simpa only [smul_inv_smul, MonoidHom.id_apply] using
      φ.kerCoeffWeilPairing_smul hn g (g⁻¹ • P) Q

/-- Evaluation of the character attached to `Q` is the isogeny Weil pairing with `Q`. -/
@[simp]
theorem toAddMonoidHom_kerCoeffWeilDual (Q : (ofIsogeny φ.dual).KerCoeff) :
    (φ.kerCoeffWeilDual hn Q).toAddMonoidHom = (φ.kerCoeffWeilPairing hn).flip Q := (rfl)

/-- The Weil dual of the projection `E₁[n] → E₂[φ̂]` is restriction of characters along
`E₁[φ] → E₁[n]`. -/
theorem kerCoeffWeilDual_comp_torsionCoeffToDualKerCoeff :
    (φ.kerCoeffWeilDual hn).comp φ.torsionCoeffToDualKerCoeff =
      (InternalHom.precomp (AbsoluteGaloisGroup K) φ.kerCoeffToTorsionCoeff).comp
        (W₁.torsionCoeffWeilDual φ.degree hn) := by
  ext R P
  simp [InternalHom.toAddMonoidHom_precomp]

/-- **Duality of the kernels of an isogeny and of its dual as Galois modules**: every character
`E₁(Kˢ)[φ] → μ_n` is `P ↦ e_φ(P, Q)` for a unique `Q ∈ E₂(Kˢ)[φ̂]`. -/
theorem kerCoeffWeilDual_bijective : Function.Bijective (φ.kerCoeffWeilDual hn) := by
  have := hn.neZero_natCast
  have : Finite (KummerCoeff K φ.degree) :=
    Finite.of_equiv _ (kummerCoeffAddEquivZMod hn).symm.toEquiv
  have hinj : Function.Injective (φ.kerCoeffWeilDual hn) := by
    refine (injective_iff_map_eq_zero _).2 fun Q hQ ↦
      φ.kerCoeffWeilPairing_nondegenerate_right hn fun P ↦ ?_
    have h := congrArg (fun f ↦ InternalHom.evalPairing (AbsoluteGaloisGroup K) f P) hQ
    simpa using h
  apply hinj.bijective_of_nat_card_le
  rw [InternalHom.natCard_of_addEquiv_zmod (kummerCoeffAddEquivZMod hn)
    φ.degree_nsmul_kerCoeff_eq_zero, φ.natCard_kerCoeff_dual hn]

/-! ### The cup product -/

/-- **The cup product along the isogeny Weil pairing**,
`H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → H²(K, μ_n)`. It is obtained from the evaluation duality map by the
identification of `E₂(Kˢ)[φ̂]` with the dual of `E₁(Kˢ)[φ]`. -/
def kerH1WeilPairing : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      H2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree) :=
  haveI := hn.neZero_natCast
  (dualityMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (KummerCoeff K φ.degree)).compl₂
    (explicitCoeff1 _ _ (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology)

/-- The isogeny Weil cup is the evaluation duality map after applying the dual coefficient map. -/
theorem kerH1WeilPairing_eq_dualityMap1 (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    haveI := hn.neZero_natCast
    φ.kerH1WeilPairing hn a b =
      dualityMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (KummerCoeff K φ.degree) a
        (explicitCoeff1 _ _ (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology b) := by
  have := hn.neZero_natCast
  rfl

/-- The pairing is the usual cup product along `e_φ`, in the order `e_φ(a(g), g • b(h))`. -/
theorem kerH1WeilPairing_eq_explicitCup11
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.kerH1WeilPairing hn a b =
      explicitCup11 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (ofIsogeny φ.dual).KerCoeff
        (KummerCoeff K φ.degree) (φ.kerCoeffWeilPairing hn) continuous_of_discreteTopology
        (φ.kerCoeffWeilPairing_smul hn) a b := by
  have := hn.neZero_natCast
  have h := explicitCoeff2_explicitCup11 (AbsoluteGaloisGroup K)
    (ofIsogeny φ).KerCoeff (ofIsogeny φ.dual).KerCoeff (KummerCoeff K φ.degree)
    (ofIsogeny φ).KerCoeff (InternalHom (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
      (KummerCoeff K φ.degree)) (KummerCoeff K φ.degree)
    (φ.kerCoeffWeilPairing hn) continuous_of_discreteTopology
    (φ.kerCoeffWeilPairing_smul hn)
    (InternalHom.evalPairing (AbsoluteGaloisGroup K)).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := AbsoluteGaloisGroup K))
    (DistribMulActionHom.id _) (φ.kerCoeffWeilDual hn) (DistribMulActionHom.id _)
    continuous_id continuous_of_discreteTopology continuous_id
    (fun _ _ ↦ by simp only [DistribMulActionHom.id_apply, AddMonoidHom.flip_apply,
      InternalHom.evalPairing_apply, toAddMonoidHom_kerCoeffWeilDual]) a b
  simpa only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply,
    kerH1WeilPairing_eq_dualityMap1, dualityMap1_eq_explicitCup11] using h.symm

private theorem explicitCoeff1_kerCoeffWeilDual_torsionCoeffToDualKerCoeff
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    explicitCoeff1 _ _ (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      explicitCoeff1 _ _ (InternalHom.precomp (AbsoluteGaloisGroup K)
        φ.kerCoeffToTorsionCoeff) continuous_of_discreteTopology
        (explicitCoeff1 _ _ (W₁.torsionCoeffWeilDual φ.degree hn)
          continuous_of_discreteTopology b) := by
  have h := congrArg (fun f ↦ explicitCoeff1 _ _ f continuous_of_discreteTopology b)
    (φ.kerCoeffWeilDual_comp_torsionCoeffToDualKerCoeff hn)
  rw [explicitCoeff1_comp _ _ φ.torsionCoeffToDualKerCoeff (φ.kerCoeffWeilDual hn)
      continuous_of_discreteTopology continuous_of_discreteTopology,
    explicitCoeff1_comp _ _ (W₁.torsionCoeffWeilDual φ.degree hn)
      (InternalHom.precomp (AbsoluteGaloisGroup K) φ.kerCoeffToTorsionCoeff)
      continuous_of_discreteTopology continuous_of_discreteTopology,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at h
  exact h

/-- The isogeny Weil cup product with a class projected from degree-torsion is the
multiplication Weil cup product with the first class included into degree-torsion. -/
theorem kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    φ.kerH1WeilPairing hn a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.torsionH1WeilPairing φ.degree hn
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b := by
  have := hn.neZero_natCast
  rw [kerH1WeilPairing_eq_dualityMap1, torsionH1WeilPairing_eq_dualityMap1,
    dualityMap1_explicitCoeff1]
  exact congrArg (dualityMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (KummerCoeff K φ.degree) a)
    (φ.explicitCoeff1_kerCoeffWeilDual_torsionCoeffToDualKerCoeff hn b)

end TauCeti.Isogeny

end
