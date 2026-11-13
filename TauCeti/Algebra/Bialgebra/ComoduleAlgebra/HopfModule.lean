/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.Antipode
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct

/-!
# Descent of relative Hopf modules along Hopf–Galois extensions

Let `H` be a commutative Hopf algebra over `R` and `A` a commutative `H`-comodule algebra, so
that the affine group scheme `G = Spec H` acts on `X = Spec A`. A **relative Hopf module** (an
`(A, H)`-Hopf module) is an `A`-module `N` with a right `H`-comodule structure for which the
action `A ⊗[R] N → N` is a morphism of comodules, `coact (a • n) = ∑ a₀ • n₀ ⊗ a₁ n₁`
(`TauCeti.IsRelativeHopfModule`). It is a `G`-equivariant quasi-coherent module on `X`; for
instance `A` is a relative Hopf module over itself.

Let `B` be an algebra acting on `A` by coinvariants, so that `X → Spec B` is `G`-invariant. The
**Galois map** of `N`,

  `A ⊗[B] N → N ⊗[R] H,  a ⊗ n ↦ a • coact n`

(`TauCeti.IsRelativeHopfModule.galoisMap`), compares the pullbacks of `N` along the two
projections `X ×_{Spec B} X ⇉ X`, transported along `X × G → X ×_{Spec B} X`,
`(x, g) ↦ (x, x g)`. For `N = A` it is the Galois map `TauCeti.ComoduleAlgebra.galoisMap` of `A`,
and the first theorem says that when this one is bijective, the Galois map of every relative Hopf
module is bijective (`TauCeti.IsRelativeHopfModule.galoisMap_bijective`). Its inverse is
`n ⊗ h ↦ ∑ β⁻¹(1 ⊗ S n₁ h) • (1 ⊗ n₀)`, where `β` is the Galois map of `A` and `S` the antipode.

The second theorem is the descent of relative Hopf modules. The **coinvariants**
`N^{co H} = {n | coact n = n ⊗ 1}` form a `B`-submodule
(`TauCeti.IsRelativeHopfModule.coinvariants`). If `A` is flat over `B` and the Galois map of `A`
is bijective, for instance if `A` is a faithfully flat `H`-Galois extension of `B`, then
`a ⊗ n ↦ a • n` is an isomorphism `A ⊗[B] N^{co H} ≃ N`
(`TauCeti.IsRelativeHopfModule.baseChangeCoinvariantsEquiv`). Geometrically, every
`G`-equivariant quasi-coherent module on a `G`-torsor `X → Y = Spec B` is the pullback of a
quasi-coherent module on `Y`, namely of its coinvariants. By flatness, `A ⊗[B] N^{co H}` is the
equalizer of the maps `A ⊗[B] N ⇉ A ⊗[B] (N ⊗[R] H)` induced by the coaction and by
`n ↦ n ⊗ 1`, and the Galois map of `N` carries this equalizer onto the elements `n ⊗ 1` of
`N ⊗[R] H`, that is, onto `N`.

## Main definitions

* `TauCeti.IsRelativeHopfModule`: an `A`-module with a compatible right `H`-comodule structure.
* `TauCeti.IsRelativeHopfModule.galoisMap`: the Galois map `A ⊗[B] N → N ⊗[R] H`.
* `TauCeti.IsRelativeHopfModule.coinvariants`: the `B`-submodule `N^{co H}`.
* `TauCeti.IsRelativeHopfModule.baseChangeCoinvariantsEquiv`: the descent isomorphism
  `A ⊗[B] N^{co H} ≃ₗ[A] N`.

## Main results

* `TauCeti.IsRelativeHopfModule.galoisMap_bijective`: the Galois map of a relative Hopf module
  is bijective when that of `A` is.
* `TauCeti.IsRelativeHopfModule.baseChangeCoinvariantsEquiv_tmul`: the descent isomorphism is
  `a ⊗ n ↦ a • n`.

## References

* H.-J. Schneider, *Principal homogeneous spaces for arbitrary Hopf algebras*, Israel J. Math.
  **72** (1990), 167–195, Theorem I.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §8.5 (relative Hopf modules, Theorem 8.5.6).
* M. Takeuchi, *Relative Hopf modules — equivalences and freeness criteria*, J. Algebra **60**
  (1979), 452–471.
-/

public section

open scoped TensorProduct

namespace TauCeti

section Defs

variable (R H A N : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring A] [Algebra R A] [ComoduleAlgebra R H A]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N] [Comodule R H N]

/-- A **relative Hopf module** over a comodule algebra `A`: an `A`-module `N` with a right
`H`-comodule structure for which the action `A ⊗[R] N → N` is a morphism of comodules, for the
diagonal coaction `TauCeti.Comodule.tensorCoact` on `A ⊗[R] N`. That is,
`coact (a • n) = ∑ a₀ • n₀ ⊗ a₁ n₁`. For commutative `H` and `A` it is a quasi-coherent module on
`Spec A` which is equivariant for the action of `Spec H`. -/
class IsRelativeHopfModule : Prop where
  /-- The coaction of `a • n` is `∑ a₀ • n₀ ⊗ a₁ n₁`. -/
  coact_smul (a : A) (n : N) :
    Comodule.coact (R := R) (C := H) (a • n) =
      (TensorProduct.lift (Algebra.lsmul R R N).toLinearMap).rTensor H
        (Comodule.tensorCoact (R := R) (C := H) (a ⊗ₜ[R] n))

/-- A comodule algebra is a relative Hopf module over itself. -/
instance IsRelativeHopfModule.self : IsRelativeHopfModule R H A A where
  coact_smul a b := by
    rw [smul_eq_mul, ComoduleAlgebra.coact_mul, Comodule.tensorCoact_tmul]
    induction Comodule.coact (R := R) (C := H) a with
    | add x y hx hy => simp only [add_mul, hx, hy, TensorProduct.add_tmul, map_add]
    | tmul a h =>
      induction Comodule.coact (R := R) (C := H) b with
      | add x y hx hy => simp only [mul_add, hx, hy, TensorProduct.tmul_add, map_add]
      | tmul b h' => simp

end Defs

/-! ### The Galois map and the coinvariants -/

namespace IsRelativeHopfModule

section Semiring

variable {R H A B N : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring A] [Algebra R A] [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

variable (R H A N) in
/-- The action `(a ⊗ h) • (n ⊗ h') = a • n ⊗ h h'` of `A ⊗[R] H` on `N ⊗[R] H`. -/
private noncomputable def tensorSMul : A ⊗[R] H →ₗ[R] N ⊗[R] H →ₗ[R] N ⊗[R] H :=
  TensorProduct.map₂ (Algebra.lsmul R R N).toLinearMap (LinearMap.mul R H)

private theorem tensorSMul_tmul_tmul (a : A) (h : H) (n : N) (h' : H) :
    tensorSMul R H A N (a ⊗ₜ h) (n ⊗ₜ h') = (a • n) ⊗ₜ (h * h') :=
  (rfl)

private theorem tensorSMul_tmul_one_mul (a : A) (u : A ⊗[R] H) (v : N ⊗[R] H) :
    tensorSMul R H A N ((a ⊗ₜ 1) * u) v = a • tensorSMul R H A N u v := by
  induction u with
  | add u u' hu hu' => simp only [mul_add, map_add, LinearMap.add_apply, hu, hu', smul_add]
  | tmul x h =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    induction v with
    | add v v' hv hv' => simp only [map_add, hv, hv', smul_add]
    | tmul n h' => simp [tensorSMul_tmul_tmul, mul_smul, TensorProduct.smul_tmul']

private theorem tensorSMul_one (v : N ⊗[R] H) : tensorSMul R H A N 1 v = v := by
  induction v with
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | tmul n h => simp [Algebra.TensorProduct.one_def, tensorSMul_tmul_tmul]

private theorem tensorSMul_one_tmul (h : H) (v : N ⊗[R] H) :
    tensorSMul R H A N (1 ⊗ₜ h) v = (LinearMap.mulLeft R h).lTensor N v := by
  induction v with
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | tmul n h' => simp [tensorSMul_tmul_tmul]

variable [ComoduleAlgebra R H A] [Comodule R H N] [IsRelativeHopfModule R H A N]

/-- The defining identity of a relative Hopf module, through the action of `A ⊗[R] H` on
`N ⊗[R] H`. -/
private theorem coact_smul_eq_tensorSMul (a : A) (n : N) :
    Comodule.coact (R := R) (C := H) (a • n) =
      tensorSMul R H A N (Comodule.coact (R := R) (C := H) a)
        (Comodule.coact (R := R) (C := H) n) := by
  rw [coact_smul, Comodule.tensorCoact_tmul]
  induction Comodule.coact (R := R) (C := H) a with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hx, hy]
  | tmul a h =>
    induction Comodule.coact (R := R) (C := H) n with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul n h' => simp [tensorSMul_tmul_tmul]

/-- The coaction of a relative Hopf module is linear over the coinvariants of `A`. -/
theorem coact_smul_of_mem_coinvariants {a : A} (ha : a ∈ ComoduleAlgebra.coinvariants R H A)
    (n : N) :
    Comodule.coact (R := R) (C := H) (a • n) = a • Comodule.coact (R := R) (C := H) n := by
  rw [coact_smul_eq_tensorSMul, ComoduleAlgebra.mem_coinvariants.1 ha,
    ← mul_one (a ⊗ₜ[R] (1 : H)), tensorSMul_tmul_one_mul, tensorSMul_one]

variable [CommSemiring B] [Algebra R B] [Algebra B A]
  [Module B N] [IsScalarTower B A N] [IsScalarTower R B N]
  (hB : ∀ b : B, algebraMap B A b ∈ ComoduleAlgebra.coinvariants R H A)

variable (B N) in
/-- The coaction of a relative Hopf module, as a `B`-linear map for an algebra `B` acting on `A`
by coinvariants. -/
noncomputable def coactLinearMap : N →ₗ[B] N ⊗[R] H where
  toFun := Comodule.coact (R := R) (C := H)
  map_add' := map_add _
  map_smul' b n := by
    rw [RingHom.id_apply, ← algebraMap_smul A b n, coact_smul_of_mem_coinvariants (hB b),
      algebraMap_smul]

@[simp]
theorem coactLinearMap_apply (n : N) :
    coactLinearMap B N hB n = Comodule.coact (R := R) (C := H) n :=
  (rfl)

variable (B N) in
/-- The **coinvariants** `N^{co H} = {n | coact n = n ⊗ 1}` of a relative Hopf module, the
equalizer of the coaction and `n ↦ n ⊗ 1`, as a submodule over an algebra `B` acting on `A` by
coinvariants. Its underlying set is the fixed subcomodule `TauCeti.Comodule.fixedSubcomodule`
(`TauCeti.IsRelativeHopfModule.coe_coinvariants`). -/
noncomputable def coinvariants : Submodule B N :=
  LinearMap.eqLocus (coactLinearMap B N hB)
    ((TensorProduct.AlgebraTensorModule.mk R B N H).flip 1)

@[simp]
theorem mem_coinvariants {n : N} :
    n ∈ coinvariants B N hB ↔ Comodule.coact (R := R) (C := H) n = n ⊗ₜ 1 :=
  Iff.rfl

/-- The coinvariants of a relative Hopf module are its fixed subcomodule. -/
theorem coe_coinvariants :
    (coinvariants B N hB : Set N) = Comodule.fixedSubcomodule R H N := by
  ext n
  simp [Comodule.mem_fixedSubcomodule]

end Semiring

section Galois

variable {R H A B N : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommSemiring A] [Algebra R A] [ComoduleAlgebra R H A]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N] [Comodule R H N]
  [IsRelativeHopfModule R H A N] [CommSemiring B] [Algebra R B] [Algebra B A]
  [Module B N] [IsScalarTower B A N] [IsScalarTower R B N]
  (hB : ∀ b : B, algebraMap B A b ∈ ComoduleAlgebra.coinvariants R H A)

variable (B N) in
/-- The **Galois map** `A ⊗[B] N → N ⊗[R] H`, `a ⊗ n ↦ a • coact n`, of a relative Hopf module,
for an algebra `B` acting on `A` by coinvariants. For `N = A` it is the Galois map
`TauCeti.ComoduleAlgebra.galoisMap` of `A` (`TauCeti.IsRelativeHopfModule.galoisMap_self`). -/
noncomputable def galoisMap : A ⊗[B] N →ₗ[A] N ⊗[R] H :=
  (coactLinearMap B N hB).liftBaseChange A

@[simp]
theorem galoisMap_tmul (a : A) (n : N) :
    galoisMap B N hB (a ⊗ₜ n) = a • Comodule.coact (R := R) (C := H) n :=
  (rfl)

/-- The Galois map of `A`, as a relative Hopf module over itself, is the Galois map of the
comodule algebra `A`. -/
theorem galoisMap_self [IsScalarTower R B A] :
    galoisMap B A hB = (ComoduleAlgebra.galoisMap B hB).toLinearMap := by
  ext a
  simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]

end Galois

section Bijective

variable {R H A B N : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommSemiring A] [Algebra R A] [ComoduleAlgebra R H A]
  [CommSemiring B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N] [Comodule R H N]
  [IsRelativeHopfModule R H A N] [Module B N] [IsScalarTower B A N] [IsScalarTower R B N]
  {hB : ∀ b : B, algebraMap B A b ∈ ComoduleAlgebra.coinvariants R H A}

variable (R B N) in
/-- `(x ⊗ y) ⊗ n ↦ x ⊗ y • n`. -/
private noncomputable def actOne : (A ⊗[B] A) ⊗[R] N →ₗ[R] A ⊗[B] N :=
  ((((LinearMap.id : N →ₗ[R] N).liftBaseChange A).restrictScalars B).lTensor A ∘ₗ
    (TensorProduct.AlgebraTensorModule.assoc R B B A A N).toLinearMap).restrictScalars R

omit [IsScalarTower R B N] in
private theorem actOne_tmul (x y : A) (n : N) :
    actOne R B N ((x ⊗ₜ[B] y) ⊗ₜ[R] n) = x ⊗ₜ[B] (y • n) :=
  (rfl)

omit [IsScalarTower R B N] in
private theorem actOne_mul_tmul (z : A ⊗[B] A) (x : A) (n : N) :
    actOne R B N ((z * (1 ⊗ₜ x)) ⊗ₜ[R] n) = actOne R B N (z ⊗ₜ[R] (x • n)) := by
  induction z with
  | add z z' hz hz' => simp only [add_mul, TensorProduct.add_tmul, map_add, hz, hz']
  | tmul a y => simp [actOne_tmul, mul_smul]

private theorem galoisMap_actOne (z : A ⊗[B] A) (n : N) :
    galoisMap B N hB (actOne R B N (z ⊗ₜ[R] n)) =
      tensorSMul R H A N (ComoduleAlgebra.galoisMap B hB z)
        (Comodule.coact (R := R) (C := H) n) := by
  induction z with
  | add z z' hz hz' => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hz, hz']
  | tmul x y =>
    rw [actOne_tmul, galoisMap_tmul, coact_smul_eq_tensorSMul, ComoduleAlgebra.galoisMap_tmul,
      tensorSMul_tmul_one_mul]

variable (hβ : Function.Bijective (ComoduleAlgebra.galoisMap B hB))

/-- The inverse `A ⊗[R] H → A ⊗[B] A` of the Galois map of `A`, restricted to `H`. -/
private noncomputable def translation : H →ₗ[R] A ⊗[B] A :=
  ((AlgEquiv.ofBijective _ hβ).symm.toLinearMap.restrictScalars R) ∘ₗ
    (Algebra.TensorProduct.includeRight : H →ₐ[R] A ⊗[R] H).toLinearMap

private theorem galoisMap_translation (h : H) :
    ComoduleAlgebra.galoisMap B hB (translation hβ h) = 1 ⊗ₜ h := by
  simp only [translation, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeRight_apply, LinearMap.coe_restrictScalars,
    AlgEquiv.toLinearMap_apply]
  exact (AlgEquiv.ofBijective _ hβ).apply_symm_apply (1 ⊗ₜ h)

variable (N) in
/-- `h ⊗ n ↦ β⁻¹(1 ⊗ h) • (1 ⊗ n)`. -/
private noncomputable def translationAct : H ⊗[R] N →ₗ[R] A ⊗[B] N :=
  actOne R B N ∘ₗ (translation hβ).rTensor N

omit [Comodule R H N] [IsRelativeHopfModule R H A N] [IsScalarTower R B N] in
private theorem translationAct_tmul (h : H) (n : N) :
    translationAct N hβ (h ⊗ₜ n) = actOne R B N (translation hβ h ⊗ₜ n) :=
  (rfl)

private theorem galoisMap_translationAct (t : H ⊗[R] N) :
    galoisMap B N hB (translationAct N hβ t) = Comodule.mulCoact R H N t := by
  induction t with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul h n =>
    rw [translationAct_tmul, galoisMap_actOne, galoisMap_translation, tensorSMul_one_tmul,
      Comodule.mulCoact_tmul]

variable (N) in
/-- The inverse of the Galois map of `N`: `n ⊗ h ↦ ∑ β⁻¹(1 ⊗ S n₁ h) • (1 ⊗ n₀)`. -/
private noncomputable def galoisMapInv : N ⊗[R] H →ₗ[R] A ⊗[B] N :=
  translationAct N hβ ∘ₗ (Comodule.mulCoactEquiv R H N).symm.toLinearMap

private theorem galoisMap_galoisMapInv (y : N ⊗[R] H) :
    galoisMap B N hB (galoisMapInv N hβ y) = y := by
  rw [galoisMapInv, LinearMap.comp_apply, galoisMap_translationAct, ← Comodule.mulCoactEquiv_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

omit [IsRelativeHopfModule R H A N] [IsScalarTower R B N] in
private theorem galoisMapInv_mulCoact (t : H ⊗[R] N) :
    galoisMapInv N hβ (Comodule.mulCoact R H N t) = translationAct N hβ t := by
  rw [galoisMapInv, LinearMap.comp_apply, ← Comodule.mulCoactEquiv_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- `h ⊗ x ↦ β⁻¹(1 ⊗ h) (1 ⊗ x)`. -/
private noncomputable def untwist : H ⊗[R] A →ₗ[R] A ⊗[B] A :=
  TensorProduct.lift ((LinearMap.mul R (A ⊗[B] A)).compl₁₂ (translation hβ)
    (Algebra.TensorProduct.includeRight.toLinearMap.restrictScalars R))

private theorem untwist_tmul (h : H) (x : A) :
    untwist hβ (h ⊗ₜ x) = translation hβ h * (1 ⊗ₜ x) :=
  (rfl)

private theorem galoisMap_untwist (t : H ⊗[R] A) :
    ComoduleAlgebra.galoisMap B hB (untwist hβ t) = Comodule.mulCoact R H A t := by
  induction t with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul h x =>
    rw [untwist_tmul, map_mul, galoisMap_translation, ComoduleAlgebra.galoisMap_tmul,
      ← Algebra.TensorProduct.one_def, one_mul, Comodule.mulCoact_tmul]
    induction Comodule.coact (R := R) (C := H) x with
    | add w w' hw hw' => simp only [mul_add, map_add, hw, hw']
    | tmul y h' => simp

/-- The element `a ⊗ 1` of `A ⊗[B] A` is `∑ β⁻¹(1 ⊗ S a₁) (1 ⊗ a₀)`. -/
private theorem untwist_antipodeShear_coact (a : A) :
    untwist hβ (Comodule.antipodeShear R H A (Comodule.coact (R := R) (C := H) a ⊗ₜ 1)) =
      a ⊗ₜ[B] (1 : A) := by
  apply hβ.1
  rw [galoisMap_untwist, Comodule.mulCoact_antipodeShear_coact, ComoduleAlgebra.galoisMap_tmul,
    ComoduleAlgebra.coact_one, mul_one]

omit [IsRelativeHopfModule R H A N] [IsScalarTower R B N] in
private theorem galoisMapInv_surjective : Function.Surjective (galoisMapInv N hβ) := by
  have key (n : N) (t : H ⊗[R] A) :
      actOne R B N (untwist hβ t ⊗ₜ n) ∈ LinearMap.range (galoisMapInv N hβ) := by
    induction t with
    | add t t' ht ht' => rw [map_add, TensorProduct.add_tmul, map_add]; exact add_mem ht ht'
    | tmul h x =>
      rw [untwist_tmul, actOne_mul_tmul, ← translationAct_tmul, ← galoisMapInv_mulCoact]
      exact LinearMap.mem_range_self _ _
  intro x
  induction x with
  | add x x' hx hx' =>
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hx'
    exact ⟨y + y', map_add _ _ _⟩
  | tmul a n =>
    have h : a ⊗ₜ[B] n = actOne R B N ((a ⊗ₜ[B] (1 : A)) ⊗ₜ[R] n) := by
      rw [actOne_tmul, one_smul]
    rw [h, ← untwist_antipodeShear_coact hβ]
    exact key n _

include hβ in
/-- **The Galois map of a relative Hopf module is bijective** when the Galois map of `A` is.
Geometrically: over a torsor `Spec A → Spec B` under `Spec H`, the two pullbacks of an
equivariant module to `Spec A ×_{Spec B} Spec A` are identified through the action. -/
theorem galoisMap_bijective : Function.Bijective (galoisMap B N hB) := by
  refine ⟨fun x x' hx ↦ ?_, fun y ↦ ⟨_, galoisMap_galoisMapInv hβ y⟩⟩
  obtain ⟨y, rfl⟩ := galoisMapInv_surjective hβ x
  obtain ⟨y', rfl⟩ := galoisMapInv_surjective hβ x'
  rw [galoisMap_galoisMapInv, galoisMap_galoisMapInv] at hx
  rw [hx]

end Bijective

section Descent

variable {R H A B N : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]
  [CommRing B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Comodule R H N]
  [IsRelativeHopfModule R H A N] [Module B N] [IsScalarTower B A N] [IsScalarTower R B N]
  {hB : ∀ b : B, algebraMap B A b ∈ ComoduleAlgebra.coinvariants R H A}

omit [IsScalarTower R B A] in
/-- The coinvariants are the equalizer of the coaction and `n ↦ n ⊗ 1`. -/
private theorem exact_coinvariants :
    Function.Exact (coinvariants B N hB).subtype
      (coactLinearMap B N hB - (TensorProduct.AlgebraTensorModule.mk R B N H).flip 1) := by
  intro n
  simp [sub_eq_zero]

/-- `A ⊗[B] (N ⊗[R] H) → (N ⊗[R] H) ⊗[R] H`, the Galois map on the first two factors. -/
private noncomputable def galoisMapRTensor : A ⊗[B] (N ⊗[R] H) →ₗ[R] (N ⊗[R] H) ⊗[R] H :=
  ((galoisMap B N hB).restrictScalars R).rTensor H ∘ₗ
    ((TensorProduct.AlgebraTensorModule.assoc R B A A N H).symm.toLinearMap.restrictScalars R)

private theorem galoisMapRTensor_tmul (a : A) (n : N) (h : H) :
    galoisMapRTensor (hB := hB) (a ⊗ₜ (n ⊗ₜ h)) = galoisMap B N hB (a ⊗ₜ n) ⊗ₜ h :=
  (rfl)

private theorem galoisMapRTensor_injective
    (hβ : Function.Bijective (ComoduleAlgebra.galoisMap B hB)) :
    Function.Injective (galoisMapRTensor (hB := hB) (N := N)) := by
  have h := ((LinearEquiv.ofBijective ((galoisMap B N hB).restrictScalars R)
    (galoisMap_bijective hβ)).rTensor H).injective
  exact h.comp (TensorProduct.AlgebraTensorModule.assoc R B A A N H).symm.injective

/-- The coaction on the right factor of `A ⊗[B] N`, read through the Galois map, is
`Δ` on the last factor. -/
private theorem galoisMapRTensor_lTensor_coact (x : A ⊗[B] N) :
    galoisMapRTensor (hB := hB) ((coactLinearMap B N hB).lTensor A x) =
      (TensorProduct.assoc R N H H).symm
        ((Coalgebra.comul (R := R) (A := H)).lTensor N (galoisMap B N hB x)) := by
  induction x with
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a n =>
    rw [LinearMap.lTensor_tmul, coactLinearMap_apply, galoisMap_tmul]
    have h₁ (v : N ⊗[R] H) : galoisMapRTensor (hB := hB) (a ⊗ₜ v) =
        a • (Comodule.coact (R := R) (C := H)).rTensor H v := by
      induction v with
      | add v v' hv hv' => simp only [TensorProduct.tmul_add, map_add, hv, hv', smul_add]
      | tmul m c => rw [galoisMapRTensor_tmul, galoisMap_tmul, LinearMap.rTensor_tmul,
          TensorProduct.smul_tmul']
    have h₂ (v : N ⊗[R] H) : a • (TensorProduct.assoc R N H H).symm
        ((Coalgebra.comul (R := R) (A := H)).lTensor N v) =
          (TensorProduct.assoc R N H H).symm
            ((Coalgebra.comul (R := R) (A := H)).lTensor N (a • v)) := by
      induction v with
      | add v v' hv hv' => simp only [map_add, smul_add, hv, hv']
      | tmul m c =>
        rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        induction Coalgebra.comul (R := R) c with
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
        | tmul x y => simp [TensorProduct.smul_tmul']
    rw [h₁, ← (TensorProduct.assoc R N H H).symm_apply_apply
      ((Comodule.coact (R := R) (C := H)).rTensor H (Comodule.coact n)), Comodule.coassoc_apply, h₂]

private theorem galoisMapRTensor_lTensor_tmulOne (x : A ⊗[B] N) :
    galoisMapRTensor (hB := hB)
        (((TensorProduct.AlgebraTensorModule.mk R B N H).flip 1).lTensor A x) =
      galoisMap B N hB x ⊗ₜ 1 := by
  induction x with
  | add x x' hx hx' => simp only [map_add, hx, hx', TensorProduct.add_tmul]
  | tmul a n => exact galoisMapRTensor_tmul a n 1

omit [IsScalarTower R B A] in
/-- The action map `A ⊗[B] N → N` is the Galois map followed by the counit. -/
private theorem liftBaseChange_id_eq (x : A ⊗[B] N) :
    (LinearMap.id : N →ₗ[B] N).liftBaseChange A x = TensorProduct.rid R N
      ((Coalgebra.counit (R := R) (A := H)).lTensor N (galoisMap B N hB x)) := by
  induction x with
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a n =>
    rw [LinearMap.liftBaseChange_tmul, LinearMap.id_apply, galoisMap_tmul]
    have (v : N ⊗[R] H) :
        TensorProduct.rid R N ((Coalgebra.counit (R := R) (A := H)).lTensor N (a • v)) =
          a • TensorProduct.rid R N ((Coalgebra.counit (R := R) (A := H)).lTensor N v) := by
      induction v with
      | add v v' hv hv' => simp only [map_add, smul_add, hv, hv']
      | tmul m c => simp [TensorProduct.smul_tmul', smul_comm a]
    simp [this]

/-- An element of `A ⊗[B] N` whose Galois map is `n ⊗ 1` is equalized by the coaction and
`n ↦ n ⊗ 1`. -/
private theorem lTensor_coact_eq_of_galoisMap_eq
    (hβ : Function.Bijective (ComoduleAlgebra.galoisMap B hB))
    {x : A ⊗[B] N} {n : N} (hx : galoisMap B N hB x = n ⊗ₜ 1) :
    (coactLinearMap B N hB).lTensor A x =
      ((TensorProduct.AlgebraTensorModule.mk R B N H).flip 1).lTensor A x := by
  apply galoisMapRTensor_injective hβ
  rw [galoisMapRTensor_lTensor_coact, galoisMapRTensor_lTensor_tmulOne, hx, LinearMap.lTensor_tmul,
    Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.assoc_symm_tmul]

/-- Conversely, the Galois map of an element of `A ⊗[B] N` equalized by the coaction and
`n ↦ n ⊗ 1` is `n ⊗ 1`, for its image `n` under the action map. -/
private theorem galoisMap_eq_of_lTensor_coact_eq {x : A ⊗[B] N}
    (hx : (coactLinearMap B N hB).lTensor A x =
      ((TensorProduct.AlgebraTensorModule.mk R B N H).flip 1).lTensor A x) :
    galoisMap B N hB x = (LinearMap.id : N →ₗ[B] N).liftBaseChange A x ⊗ₜ 1 := by
  have h := congr(galoisMapRTensor (hB := hB) $hx)
  rw [galoisMapRTensor_lTensor_coact, galoisMapRTensor_lTensor_tmulOne] at h
  -- Contract the middle factor with the counit.
  let F : (N ⊗[R] H) ⊗[R] H →ₗ[R] N ⊗[R] H :=
    (TensorProduct.lid R H ∘ₗ (Coalgebra.counit (R := R) (A := H)).rTensor H).lTensor N ∘ₗ
      (TensorProduct.assoc R N H H).toLinearMap
  have e₁ (v : N ⊗[R] H) :
      F ((TensorProduct.assoc R N H H).symm
        ((Coalgebra.comul (R := R) (A := H)).lTensor N v)) = v := by
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc, Coalgebra.rTensor_counit_comp_comul]
    induction v with
    | add v v' hv hv' => simp only [map_add, hv, hv']
    | tmul m c => simp
  have e₂ (v : N ⊗[R] H) : F (v ⊗ₜ 1) =
      TensorProduct.rid R N ((Coalgebra.counit (R := R) (A := H)).lTensor N v) ⊗ₜ 1 := by
    induction v with
    | add v v' hv hv' => simp only [map_add, TensorProduct.add_tmul, hv, hv']
    | tmul m c => simp [F, TensorProduct.smul_tmul']
  rw [liftBaseChange_id_eq (H := H) (hB := hB), ← e₂, ← h, e₁]

variable [Module.Flat B A]

/-- **Descent along a Hopf–Galois extension.** If `A` is flat over an algebra `B` acting by
coinvariants and the Galois map `A ⊗[B] A → A ⊗[R] H` is bijective, then every relative Hopf
module `N` is the base change of its coinvariants: `a ⊗ n ↦ a • n` is an isomorphism
`A ⊗[B] N^{co H} ≃ N`. -/
noncomputable def baseChangeCoinvariantsEquiv
    (hβ : Function.Bijective (ComoduleAlgebra.galoisMap B hB)) :
    A ⊗[B] coinvariants B N hB ≃ₗ[A] N :=
  LinearEquiv.ofBijective ((coinvariants B N hB).subtype.liftBaseChange A) <| by
    set ι := (coinvariants B N hB).subtype
    have hex := Module.Flat.lTensor_exact A
      (exact_coinvariants (R := R) (H := H) (N := N) (hB := hB))
    have hι : Function.Injective (ι.lTensor A) :=
      Module.Flat.lTensor_preserves_injective_linearMap ι Subtype.val_injective
    have hμ (y : A ⊗[B] coinvariants B N hB) :
        ι.liftBaseChange A y = (LinearMap.id : N →ₗ[B] N).liftBaseChange A (ι.lTensor A y) := by
      induction y with
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul a n => simp [ι]
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ hι ?_, fun n ↦ ?_⟩
    · -- An element of `A ⊗[B] N^{co H}` killed by the action map has Galois map `0`.
      have hker := (hex (ι.lTensor A y)).2 ⟨y, rfl⟩
      rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero] at hker
      rw [map_zero]
      apply (galoisMap_bijective (N := N) hβ).1
      rw [galoisMap_eq_of_lTensor_coact_eq hker, ← hμ, hy, TensorProduct.zero_tmul, map_zero]
    · -- The preimage of `n ⊗ 1` under the Galois map lies in `A ⊗[B] N^{co H}`.
      obtain ⟨x, hx⟩ := (galoisMap_bijective (N := N) hβ).2 (n ⊗ₜ 1)
      obtain ⟨y, rfl⟩ := (hex x).1 (by
        rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
          lTensor_coact_eq_of_galoisMap_eq hβ hx])
      refine ⟨y, ?_⟩
      rw [hμ, liftBaseChange_id_eq (H := H) (hB := hB), hx]
      simp

@[simp]
theorem baseChangeCoinvariantsEquiv_tmul
    (hβ : Function.Bijective (ComoduleAlgebra.galoisMap B hB)) (a : A) (n : coinvariants B N hB) :
    baseChangeCoinvariantsEquiv hβ (a ⊗ₜ n) = a • (n : N) :=
  (rfl)

end Descent

end IsRelativeHopfModule

end TauCeti
