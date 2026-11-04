/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Derivation
public import TauCeti.Algebra.Lie.UniversalEnveloping.SemiDirect

/-!
# The extended affine algebra and its level enveloping algebras

Let `ĝ = L((t)) ⊕ R K` be the residue central extension of an invariant symmetric form `Φ` on a
Lie algebra `L` over a commutative ring `R`. The **extended affine algebra**
`ĝ' = ĝ ⋊ R d` adjoins the degree derivation `d = t d/dt`
(`TauCeti.CurrentAlgebra.vectorFieldExtensionDerivation` for `h = t`) to `ĝ`, as Mathlib's
semidirect sum (`TauCeti.CurrentAlgebra.extendedResidueExtension`). In it

`⁅d, x_n⁆ = n x_n` and `⁅d, K⁆ = 0`,

for the modes `x_n = tⁿ ⊗ x`, and `K` is still central.

For a scalar `a`, write `U = U(ĝ) / (ι K - a)` and `U' = U(ĝ') / (ι K - a)`. The derivation `d`
of `ĝ` lifts to the derivation `vectorFieldEnvelopingDerivation` of `U`, so by
`TauCeti.UniversalEnvelopingAlgebra.CentralQuotient.semiDirectSumOreEquiv` the algebra `U'` is the
differential operator ring `U[X; d]` (`TauCeti.CurrentAlgebra.extendedEnvelopingOreEquiv`). Hence:

* the algebra map `U → U'` induced by `ĝ → ĝ'` is injective, over every commutative ring and for
  every `a`, including `a = 0` (`TauCeti.CurrentAlgebra.toExtendedEnveloping_injective`);
* `U'` is a free left `U`-module on the powers `dⁿ`: the isomorphism carries the left monomial
  basis `x Xⁿ` of the Ore extension to `x dⁿ`
  (`TauCeti.CurrentAlgebra.extendedEnvelopingOreEquiv_symm_monomial`);
* inner derivation by `d` restricts on `U` to the lifted degree derivation, and on the current
  generators `[d, ι(x_n)] = n ι(x_n)`
  (`TauCeti.CurrentAlgebra.ι_degreeElement_mul_sub_mul_envelopingι_single_tmul`).

Since the level comparison `levelEnvelopingEquiv` between `U(ĝ_Ψ) / (ι K - 1)` and
`U(ĝ_Φ) / (ι K - k)` for `Ψ = k • Φ` commutes with the degree derivations, it extends to an algebra
isomorphism between the corresponding enveloping algebras of the extended affine algebras, fixing
`d` (`TauCeti.CurrentAlgebra.extendedLevelEnvelopingEquiv`). This holds for every `k`, including
`k = 0`; it is an isomorphism of algebras, not one induced by a Lie algebra isomorphism.

The forms use Mathlib's residue convention `Res(f dg) Φ(x, y)`; the affine convention with level
form `κ` is the case `Φ = -κ`.

## Main definitions

* `TauCeti.CurrentAlgebra.extendedResidueExtension`: the extended affine algebra `ĝ ⋊ R d`.
* `TauCeti.CurrentAlgebra.toExtendedResidueExtension` and
  `TauCeti.CurrentAlgebra.degreeElement`: the inclusion of `ĝ` and the adjoined element `d`.
* `TauCeti.CurrentAlgebra.toExtendedEnveloping`: the algebra map `U → U'`.
* `TauCeti.CurrentAlgebra.extendedEnvelopingOreEquiv`: the isomorphism `U' ≃ U[X; d]`.
* `TauCeti.CurrentAlgebra.extendedLevelEnvelopingEquiv`: the level comparison for `U'`.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the extended affine
  algebra obtained by adjoining the derivation `t d/dt` to the affine central extension.
-/

public section

noncomputable section

open scoped LaurentSeries TensorProduct
open HahnSeries LieAlgebra LieAlgebra.SemiDirectSum TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement centralElement_mem_center envelopingι)

-- The coefficientwise algebra structure matches the module used by the tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

-- The ring of scalars is the one-dimensional abelian Lie algebra spanned by `d`, and associative
-- algebras are Lie algebras under the commutator.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "C" => currentAlgebra R L

/-! ### The extended affine algebra -/

section Extension

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "E" => ofTwoCocycle c
local notation "δ" => vectorFieldExtensionDerivation Φ hΦ hΦs (single 1 1)
local notation "ψ" => LieDerivation.lineHom (vectorFieldExtensionDerivation Φ hΦ hΦs (single 1 1))

/-- **The extended affine algebra** `ĝ ⋊ R d`: the residue central extension `ĝ = L((t)) ⊕ R K` of
`Φ` with the degree derivation `d = t d/dt` adjoined, so that `⁅d, x_n⁆ = n x_n` and
`⁅d, K⁆ = 0`. -/
def extendedResidueExtension : Type _ :=
  E ⋊⁅(vectorFieldExtensionDerivation Φ hΦ hΦs (single 1 1)).lineHom⁆ R

instance : LieRing (extendedResidueExtension Φ hΦ hΦs) :=
  inferInstanceAs (LieRing (E ⋊⁅ψ⁆ R))

instance : LieAlgebra R (extendedResidueExtension Φ hΦ hΦs) :=
  inferInstanceAs (LieAlgebra R (E ⋊⁅ψ⁆ R))

local notation "E'" => extendedResidueExtension Φ hΦ hΦs

/-- The inclusion of the residue central extension `ĝ` in the extended affine algebra. -/
def toExtendedResidueExtension : E →ₗ⁅R⁆ E' :=
  inl ψ

/-- The adjoined degree element `d` of the extended affine algebra. -/
def degreeElement : E' :=
  inr ψ (1 : R)

/-- The inclusion of `ĝ` in the extended affine algebra is injective. -/
theorem toExtendedResidueExtension_injective :
    Function.Injective (toExtendedResidueExtension Φ hΦ hΦs) :=
  inl_injective ψ

/-- Every element of the extended affine algebra is `x + t • d` for some `x ∈ ĝ` and `t ∈ R`. -/
theorem exists_eq_add_smul_degreeElement (y : E') :
    ∃ (x : E) (t : R), y = toExtendedResidueExtension Φ hΦ hΦs x + t • degreeElement Φ hΦ hΦs :=
  -- The decomposition `y = inl y.left + y.right • inr 1` of the underlying semidirect sum.
  have h (y : E ⋊⁅ψ⁆ R) : y = inl ψ y.left + y.right • inr ψ 1 := by ext <;> simp
  ⟨_, _, h y⟩

/-- **The degree element acts by the degree derivation**: `⁅d, x⁆ = t x'` for `x ∈ ĝ`. -/
theorem lie_degreeElement_toExtendedResidueExtension (x : E) :
    ⁅degreeElement Φ hΦ hΦs, toExtendedResidueExtension Φ hΦ hΦs x⁆ =
      toExtendedResidueExtension Φ hΦ hΦs (δ x) :=
  LieDerivation.lie_inr_lineHom_one_inl δ x

/-- **The degree element on modes**: `⁅d, x_n⁆ = n x_n` for `x_n = r tⁿ ⊗ x`. -/
theorem lie_degreeElement_toExtendedResidueExtension_ofProd_single_tmul (n : ℤ) (r : R) (x : L) :
    ⁅degreeElement Φ hΦ hΦs, toExtendedResidueExtension Φ hΦ hΦs (ofProd c (single n r ⊗ₜ x, 0))⁆ =
      n • toExtendedResidueExtension Φ hΦ hΦs (ofProd c (single n r ⊗ₜ x, 0)) := by
  have h : ofProd c (n • (single n r ⊗ₜ x), 0) = n • ofProd c (single n r ⊗ₜ x, 0) := by
    simpa [coe_ofProdLinearEquiv] using map_zsmul (ofProdLinearEquiv c) n (single n r ⊗ₜ x, 0)
  rw [lie_degreeElement_toExtendedResidueExtension, vectorFieldExtensionDerivation_ofProd,
    vectorFieldDerivation_single_one_single_tmul, h, map_zsmul]

/-- **The degree element commutes with `K`.** -/
@[simp]
theorem lie_degreeElement_centralElement :
    ⁅degreeElement Φ hΦ hΦs,
      toExtendedResidueExtension Φ hΦ hΦs (centralElement c)⁆ = 0 := by
  rw [lie_degreeElement_toExtendedResidueExtension, vectorFieldExtensionDerivation_centralElement,
    map_zero]

/-- **`K` is central in the extended affine algebra.** -/
theorem toExtendedResidueExtension_centralElement_mem_center :
    toExtendedResidueExtension Φ hΦ hΦs (centralElement c) ∈ center R E' := by
  refine (LieModule.mem_maxTrivSubmodule R E' E' _).2 fun y ↦ ?_
  obtain ⟨x, t, rfl⟩ := exists_eq_add_smul_degreeElement Φ hΦ hΦs y
  rw [add_lie, smul_lie, lie_degreeElement_centralElement, smul_zero, add_zero, ← LieHom.map_lie,
    (LieModule.mem_maxTrivSubmodule R E E _).1 (centralElement_mem_center c) x, map_zero]

end Extension

/-! ### Its level enveloping algebras -/

section Enveloping

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => CentralQuotient R (centralElement c) a
local notation "UK'" =>
  CentralQuotient R (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) a
local notation "dU" => vectorFieldEnvelopingDerivation Φ hΦ hΦs a (single 1 1)

/-- The algebra map `U(ĝ) / (ι K - a) → U(ĝ') / (ι K - a)` induced by the inclusion of `ĝ` in the
extended affine algebra `ĝ'`. -/
def toExtendedEnveloping : UK →ₐ[R] UK' :=
  CentralQuotient.map (toExtendedResidueExtension Φ hΦ hΦs) rfl

/-- The map `U → U'` is the inclusion of `ĝ` on generators. -/
@[simp]
theorem toExtendedEnveloping_ι (x : ofTwoCocycle c) :
    toExtendedEnveloping Φ hΦ hΦs a (CentralQuotient.ι (centralElement c) a x) =
      CentralQuotient.ι _ a (toExtendedResidueExtension Φ hΦ hΦs x) :=
  CentralQuotient.map_ι _ _ x

/-- **The level enveloping algebra of the extended affine algebra is a differential operator
ring.** `U(ĝ') / (ι K - a)` is the Ore extension of `U(ĝ) / (ι K - a)` by the lifted degree
derivation `t d/dt`, with `d` corresponding to the variable `X`. -/
def extendedEnvelopingOreEquiv :
    UK' ≃ₐ[R] OreExtension (AlgHom.id R UK) (derivationLieAlgebra.toSigmaDerivation dU) :=
  CentralQuotient.semiDirectSumOreEquiv (vectorFieldEnvelopingDerivation_ι Φ hΦ hΦs a (single 1 1))

/-- The isomorphism `U' ≃ U[X; d]` sends the image of `x ∈ U` to the constant `C x`. -/
@[simp]
theorem extendedEnvelopingOreEquiv_toExtendedEnveloping (x : UK) :
    extendedEnvelopingOreEquiv Φ hΦ hΦs a (toExtendedEnveloping Φ hΦ hΦs a x) = OreExtension.C x :=
  CentralQuotient.semiDirectSumOreEquiv_map_inl _ x

/-- The isomorphism `U' ≃ U[X; d]` sends `d` to the variable `X`. -/
@[simp]
theorem extendedEnvelopingOreEquiv_ι_degreeElement :
    extendedEnvelopingOreEquiv Φ hΦ hΦs a (CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs)) =
      OreExtension.X :=
  CentralQuotient.semiDirectSumOreEquiv_ι_inr_one _

/-- **`U'` is free over `U` on the powers of `d`**: the inverse isomorphism sends the monomial
`x Xⁿ` to `x dⁿ`. -/
@[simp]
theorem extendedEnvelopingOreEquiv_symm_monomial (n : ℕ) (x : UK) :
    (extendedEnvelopingOreEquiv Φ hΦ hΦs a).symm (OreExtension.monomial n x) =
      toExtendedEnveloping Φ hΦ hΦs a x *
        CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs) ^ n :=
  CentralQuotient.semiDirectSumOreEquiv_symm_monomial _ n x

/-- **`U(ĝ) / (ι K - a)` embeds in `U(ĝ') / (ι K - a)`**, over every commutative ring and for every
central value `a`, including `a = 0`. -/
theorem toExtendedEnveloping_injective : Function.Injective (toExtendedEnveloping Φ hΦ hΦs a) :=
  CentralQuotient.map_inl_injective (vectorFieldEnvelopingDerivation_ι Φ hΦ hΦs a (single 1 1))

/-- **Inner derivation by `d` restricts to the degree derivation**: in `U'`,
`d x - x d` is the image of `t x'` for every `x ∈ U`. -/
theorem ι_degreeElement_mul_sub_mul (x : UK) :
    CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs) * toExtendedEnveloping Φ hΦ hΦs a x -
        toExtendedEnveloping Φ hΦ hΦs a x * CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs) =
      toExtendedEnveloping Φ hΦ hΦs a ((dU : Module.End R UK) x) := by
  rw [sub_eq_iff_eq_add']
  exact CentralQuotient.ι_inr_mul_map_inl
    (vectorFieldEnvelopingDerivation_ι Φ hΦ hΦs a (single 1 1)) x

/-- **The degree element on the mode generators**: `[d, ι(x_n)] = n ι(x_n)` in `U'`. -/
theorem ι_degreeElement_mul_sub_mul_envelopingι_single_tmul (n : ℤ) (r : R) (x : L) :
    CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs) *
          toExtendedEnveloping Φ hΦ hΦs a (envelopingι c a (single n r ⊗ₜ x)) -
        toExtendedEnveloping Φ hΦ hΦs a (envelopingι c a (single n r ⊗ₜ x)) *
          CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs) =
      n • toExtendedEnveloping Φ hΦ hΦs a (envelopingι c a (single n r ⊗ₜ x)) := by
  rw [ι_degreeElement_mul_sub_mul,
    vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul, map_zsmul]

end Enveloping

/-! ### The level comparison -/

section Level

variable {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) {k : R}

local notation "cΦ" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R L Ψ hΨ hΨs

/-- **The level comparison for the extended affine algebra.** If `Ψ = k • Φ`, the level comparison
`levelEnvelopingEquiv` extends, fixing `d`, to an algebra isomorphism from
`U(ĝ'_Ψ) / (ι K - 1)` to `U(ĝ'_Φ) / (ι K - k)`. This holds for every `k`, including `k = 0`. -/
def extendedLevelEnvelopingEquiv (h : Ψ = k • Φ) :
    CentralQuotient R (toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ)) 1 ≃ₐ[R]
      CentralQuotient R (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) k :=
  -- The level comparison commutes with the identity twists and with the degree derivations.
  have hσ (x : CentralQuotient R (centralElement cΨ) 1) :
      levelEnvelopingEquiv hΦ hΦs hΨ hΨs h (AlgHom.id R _ x) =
        AlgHom.id R _ (levelEnvelopingEquiv hΦ hΦs hΨ hΨs h x) := by
    rw [AlgHom.id_apply, AlgHom.id_apply]
  have hδ (x : CentralQuotient R (centralElement cΨ) 1) :
      levelEnvelopingEquiv hΦ hΦs hΨ hΨs h (derivationLieAlgebra.toSigmaDerivation
          (vectorFieldEnvelopingDerivation Ψ hΨ hΨs 1 (single 1 1)) x) =
        derivationLieAlgebra.toSigmaDerivation
          (vectorFieldEnvelopingDerivation Φ hΦ hΦs k (single 1 1))
          (levelEnvelopingEquiv hΦ hΦs hΨ hΨs h x) := by
    rw [derivationLieAlgebra.coe_toSigmaDerivation, derivationLieAlgebra.coe_toSigmaDerivation]
    exact levelEnvelopingEquiv_vectorFieldEnvelopingDerivation hΦ hΦs hΨ hΨs h _ x
  ((extendedEnvelopingOreEquiv Ψ hΨ hΨs 1).trans
    (OreExtension.mapAlgEquiv (levelEnvelopingEquiv hΦ hΦs hΨ hΨs h) hσ hδ)).trans
      (extendedEnvelopingOreEquiv Φ hΦ hΦs k).symm

/-- On the image of `U(ĝ_Ψ) / (ι K - 1)`, the extended level comparison is the level
comparison. -/
@[simp]
theorem extendedLevelEnvelopingEquiv_toExtendedEnveloping (h : Ψ = k • Φ)
    (x : CentralQuotient R (centralElement cΨ) 1) :
    extendedLevelEnvelopingEquiv hΦ hΦs hΨ hΨs h (toExtendedEnveloping Ψ hΨ hΨs 1 x) =
      toExtendedEnveloping Φ hΦ hΦs k (levelEnvelopingEquiv hΦ hΦs hΨ hΨs h x) := by
  rw [extendedLevelEnvelopingEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    extendedEnvelopingOreEquiv_toExtendedEnveloping, OreExtension.mapAlgEquiv_C,
    AlgEquiv.symm_apply_eq, extendedEnvelopingOreEquiv_toExtendedEnveloping]

/-- The extended level comparison fixes the degree element `d`. -/
@[simp]
theorem extendedLevelEnvelopingEquiv_ι_degreeElement (h : Ψ = k • Φ) :
    extendedLevelEnvelopingEquiv hΦ hΦs hΨ hΨs h
        (CentralQuotient.ι _ 1 (degreeElement Ψ hΨ hΨs)) =
      CentralQuotient.ι _ k (degreeElement Φ hΦ hΦs) := by
  rw [extendedLevelEnvelopingEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    extendedEnvelopingOreEquiv_ι_degreeElement, OreExtension.mapAlgEquiv_X, AlgEquiv.symm_apply_eq,
    extendedEnvelopingOreEquiv_ι_degreeElement]

/-- On the image of `U(ĝ_Φ) / (ι K - k)`, the inverse extended level comparison is the inverse
level comparison. -/
@[simp]
theorem extendedLevelEnvelopingEquiv_symm_toExtendedEnveloping (h : Ψ = k • Φ)
    (x : CentralQuotient R (centralElement cΦ) k) :
    (extendedLevelEnvelopingEquiv hΦ hΦs hΨ hΨs h).symm (toExtendedEnveloping Φ hΦ hΦs k x) =
      toExtendedEnveloping Ψ hΨ hΨs 1 ((levelEnvelopingEquiv hΦ hΦs hΨ hΨs h).symm x) := by
  rw [AlgEquiv.symm_apply_eq, extendedLevelEnvelopingEquiv_toExtendedEnveloping,
    AlgEquiv.apply_symm_apply]

/-- The inverse extended level comparison fixes the degree element `d`. -/
@[simp]
theorem extendedLevelEnvelopingEquiv_symm_ι_degreeElement (h : Ψ = k • Φ) :
    (extendedLevelEnvelopingEquiv hΦ hΦs hΨ hΨs h).symm
        (CentralQuotient.ι _ k (degreeElement Φ hΦ hΦs)) =
      CentralQuotient.ι _ 1 (degreeElement Ψ hΨ hΨs) := by
  rw [AlgEquiv.symm_apply_eq, extendedLevelEnvelopingEquiv_ι_degreeElement]

end Level

end TauCeti.CurrentAlgebra
