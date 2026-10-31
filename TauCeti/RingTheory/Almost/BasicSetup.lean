/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.Tactic.LinearCombination

/-!
# Basic setups for almost mathematics

Almost mathematics in the sense of Gabber–Ramero is developed relative to a *basic setup*
`(V, m)`: a commutative ring `V` with an ideal `m` such that `m * m = m` and such that
`m~ := m ⊗[V] m` is a flat `V`-module. A `V`-module is *almost zero* if it is killed by `m`, and a
linear map is an *almost isomorphism* if its kernel and cokernel are almost zero. Idempotence of
`m` is what makes almost zero modules stable under extensions, and flatness of `m~` is what makes
the left adjoint `M ↦ M_! = m~ ⊗[V] M` of the functor of almost elements exact. A basic setup is
data rather than a type class, because one ring carries several setups: for a perfectoid Tate
ring `R` one uses both `(R°, R°°)` and the ideal of compatible `p`-power roots of a
pseudouniformiser.

## Main definitions

* `TauCeti.Almost.BasicSetup`: a basic setup `(V, m)`.
* `TauCeti.Almost.BasicSetup.tilde`: the flat `V`-module `m~ = m ⊗[V] m`, with the multiplication
  maps `tildeMul : m~ → V` and `tildeToIdeal : m~ → m`.
* `TauCeti.Almost.BasicSetup.IsAlmostZero`: a module killed by `m`, and the corresponding object
  property `TauCeti.Almost.BasicSetup.almostZero` of `ModuleCat V`.
* `TauCeti.Almost.BasicSetup.IsAlmostIso`: a linear map with almost zero kernel and cokernel.
* `TauCeti.Almost.BasicSetup.classical`, `TauCeti.Almost.BasicSetup.zero`: the setups `(V, V)`,
  which recovers ordinary commutative algebra, and `(V, 0)`, for which every module is almost
  zero.
* `TauCeti.Almost.BasicSetup.IsFilteredPrincipal`, `TauCeti.Almost.BasicSetup.PowersGenerate`:
  Gabber–Ramero's conditions (A) (`m` is a directed union of principal ideals) and (B) (for every
  `k ≥ 1` the `k`-th powers of elements of `m` generate `m`).

## Main results

* `TauCeti.Almost.BasicSetup.isAlmostZero_iff_subsingleton_ideal_tensor` and
  `TauCeti.Almost.BasicSetup.isAlmostZero_iff_subsingleton_tilde_tensor`: `M` is almost zero iff
  `m ⊗[V] M = 0` iff `m~ ⊗[V] M = 0`.
* `TauCeti.Almost.BasicSetup.IsAlmostZero.of_injective`,
  `TauCeti.Almost.BasicSetup.IsAlmostZero.of_surjective` and `LinearEquiv.isAlmostZero_iff`:
  submodules, quotients and isomorphic copies of almost zero modules are almost zero.
* `TauCeti.Almost.BasicSetup.IsAlmostZero.tensorProduct`,
  `TauCeti.Almost.BasicSetup.IsAlmostZero.linearMap_of_domain` and
  `TauCeti.Almost.BasicSetup.IsAlmostZero.linearMap_of_codomain`: almost zero modules form a
  tensor ideal, stable under `P ⊗[V] -` and under `Hom` into and out of any module.
* `TauCeti.Almost.BasicSetup.isAlmostZero_classical_iff` and
  `TauCeti.Almost.BasicSetup.isAlmostIso_classical_iff`: in the classical setup, almost zero means
  zero and an almost isomorphism is a bijective linear map.
* `TauCeti.Almost.BasicSetup.isAlmostIso_subtype`: the inclusion `m → V` is an almost
  isomorphism.
* `TauCeti.Almost.BasicSetup.IsFilteredPrincipal.powersGenerate`: condition (A) implies
  condition (B).
* `TauCeti.Almost.BasicSetup.flat_tilde_of_isFilteredPrincipal`: an idempotent ideal satisfying
  condition (A) has flat `m~`, so it underlies a basic setup, with no regularity assumption on its
  elements.
* `TauCeti.Almost.BasicSetup.tildeToIdeal_bijective_of_flat`: if `m` is flat, the multiplication
  map `m~ → m` is bijective.
* `Submodule.mulMap_top_top_bijective`: the multiplication map `R ⊗[R] R → R` is bijective; it
  makes `(V, V)` a basic setup.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.1:
  (2.1.1), Example 2.1.2, (2.1.3), Remark 2.1.4, (2.1.6) and Proposition 2.1.7.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1.
-/

public section

open TensorProduct

/-- The multiplication map `R ⊗[R] R → R` of the top submodule of `R` is the identification
`R ⊗[R] R ≃ R`, hence bijective. -/
theorem Submodule.mulMap_top_top_bijective {R : Type*} [CommSemiring R] :
    Function.Bijective (Submodule.mulMap (⊤ : Submodule R R) (⊤ : Submodule R R)) := by
  have : Submodule.mulMap (⊤ : Submodule R R) (⊤ : Submodule R R) =
      ((TensorProduct.congr Submodule.topEquiv Submodule.topEquiv).trans
        (TensorProduct.lid R R)).toLinearMap :=
    TensorProduct.ext' fun x y ↦ by simp
  rw [this]
  exact LinearEquiv.bijective _

namespace TauCeti.Almost

universe u v

/-- A *basic setup* `(V, m)` for almost mathematics: an ideal `m` of the commutative ring `V`
with `m * m = m` such that `m~ = m ⊗[V] m` is a flat `V`-module (Gabber–Ramero (2.1.1) and the
standing assumption of (2.5.14)). It is data, not a class: one ring carries several setups. -/
@[ext]
structure BasicSetup (V : Type u) [CommRing V] where
  /-- The ideal `m` of the basic setup. -/
  ideal : Ideal V
  /-- The ideal is idempotent: `m * m = m` in the semiring `Ideal V`. -/
  isIdempotentElem : IsIdempotentElem ideal
  /-- The `V`-module `m~ = m ⊗[V] m` is flat. -/
  flat_tilde : Module.Flat V (ideal ⊗[V] ideal)

namespace BasicSetup

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-! ### The module `m~` -/

/-- The `V`-module `m~ = m ⊗[V] m` of a basic setup (Gabber–Ramero (2.1.1)). -/
abbrev tilde : Type u := S.ideal ⊗[V] S.ideal

instance : Module.Flat V S.tilde := S.flat_tilde

/-- The multiplication map `m~ → V`, `x ⊗ y ↦ x * y`. -/
noncomputable def tildeMul : S.tilde →ₗ[V] V := Submodule.mulMap S.ideal S.ideal

@[simp]
theorem tildeMul_tmul (x y : S.ideal) : S.tildeMul (x ⊗ₜ y) = x * y :=
  Submodule.mulMap_tmul _ _ x y

/-- The image of the multiplication map `m~ → V` is `m`, because `m * m = m`. -/
@[simp]
theorem range_tildeMul : LinearMap.range S.tildeMul = S.ideal :=
  (Submodule.mulMap_range S.ideal S.ideal).trans S.isIdempotentElem.eq

/-- The multiplication map `m~ → m`, `x ⊗ y ↦ x * y`, which is surjective because `m * m = m`. -/
noncomputable def tildeToIdeal : S.tilde →ₗ[V] S.ideal :=
  (LinearEquiv.ofEq _ _ S.isIdempotentElem.eq).toLinearMap ∘ₗ Submodule.mulMap' S.ideal S.ideal

@[simp]
theorem coe_tildeToIdeal (t : S.tilde) : (S.tildeToIdeal t : V) = S.tildeMul t :=
  -- `Submodule.mulMap'` and `LinearEquiv.ofEq` only restrict the codomain of `Submodule.mulMap`.
  (rfl)

@[simp]
theorem tildeToIdeal_tmul (x y : S.ideal) :
    S.tildeToIdeal (x ⊗ₜ y) = ⟨x * y, S.ideal.mul_mem_left _ y.2⟩ :=
  Subtype.ext (by simp)

theorem tildeToIdeal_surjective : Function.Surjective S.tildeToIdeal := by
  rw [tildeToIdeal, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp (Submodule.mulMap'_surjective S.ideal S.ideal)

/-- If the ideal `m` is a flat `V`-module, the multiplication map `m~ → m` is bijective, so that
`m~` is just `m` (Gabber–Ramero (2.1.1)). -/
theorem tildeToIdeal_bijective_of_flat [Module.Flat V S.ideal] :
    Function.Bijective S.tildeToIdeal := by
  refine ⟨fun s t hst ↦ ?_, S.tildeToIdeal_surjective⟩
  have hdisj : S.ideal.LinearDisjoint S.ideal :=
    .of_right_le_one_of_flat _ _ (le_top.trans_eq Ideal.one_eq_top.symm)
  exact hdisj.injective (by simpa only [coe_tildeToIdeal, tildeMul] using congrArg Subtype.val hst)

/-! ### Almost zero modules -/

/-- A `V`-module `M` is *almost zero* for the basic setup `S` if it is killed by the ideal `m`
(Gabber–Ramero (2.1.3)), that is, if it is `m`-torsion in the sense of
`Module.IsTorsionBySet`. -/
def IsAlmostZero (M : Type*) [AddCommGroup M] [Module V M] : Prop :=
  Module.IsTorsionBySet V M S.ideal

variable {S} in
theorem isAlmostZero_iff_isTorsionBySet {M : Type*} [AddCommGroup M] [Module V M] :
    S.IsAlmostZero M ↔ Module.IsTorsionBySet V M S.ideal :=
  Iff.rfl

variable {S} in
theorem isAlmostZero_iff {M : Type*} [AddCommGroup M] [Module V M] :
    S.IsAlmostZero M ↔ ∀ ε ∈ S.ideal, ∀ x : M, ε • x = 0 :=
  ⟨fun h ε hε x ↦ @h x ⟨ε, hε⟩, fun h x ε ↦ h ε ε.2 x⟩

variable {S} in
theorem IsAlmostZero.smul_eq_zero {M : Type*} [AddCommGroup M] [Module V M]
    (h : S.IsAlmostZero M) {ε : V} (hε : ε ∈ S.ideal) (x : M) : ε • x = 0 :=
  isAlmostZero_iff.mp h ε hε x

@[simp]
theorem isAlmostZero_of_subsingleton {M : Type*} [AddCommGroup M] [Module V M]
    [Subsingleton M] : S.IsAlmostZero M :=
  isAlmostZero_iff.mpr fun _ _ _ ↦ Subsingleton.elim _ _

/-- The quotient `V ⧸ m` is almost zero. -/
@[simp]
theorem isAlmostZero_quotient : S.IsAlmostZero (V ⧸ S.ideal) :=
  (Module.isTorsionBySet_quotient_iff _ _).mpr fun _ _ hε ↦ S.ideal.mul_mem_right _ hε

variable {S} in
/-- A module that embeds into an almost zero module is almost zero; in particular, so is every
submodule of an almost zero module. -/
theorem IsAlmostZero.of_injective {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N]
    [Module V N] (h : S.IsAlmostZero N) {f : M →ₗ[V] N} (hf : Function.Injective f) :
    S.IsAlmostZero M :=
  isAlmostZero_iff.mpr fun ε hε x ↦ hf <| by rw [map_smul, h.smul_eq_zero hε, map_zero]

variable {S} in
/-- A quotient of an almost zero module is almost zero. -/
theorem IsAlmostZero.of_surjective {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N]
    [Module V N] (h : S.IsAlmostZero M) {f : M →ₗ[V] N} (hf : Function.Surjective f) :
    S.IsAlmostZero N :=
  isAlmostZero_iff.mpr fun ε hε y ↦ by
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_smul, h.smul_eq_zero hε, map_zero]

/-- Being almost zero is invariant under linear equivalence. -/
theorem _root_.LinearEquiv.isAlmostZero_iff {M N : Type*} [AddCommGroup M] [Module V M]
    [AddCommGroup N] [Module V N] (e : M ≃ₗ[V] N) : S.IsAlmostZero M ↔ S.IsAlmostZero N :=
  ⟨fun h ↦ h.of_surjective e.surjective, fun h ↦ h.of_injective e.injective⟩

variable {S} in
/-- A tensor product with an almost zero module is almost zero. -/
theorem IsAlmostZero.tensorProduct {M : Type*} [AddCommGroup M] [Module V M]
    (P : Type*) [AddCommGroup P] [Module V P] (h : S.IsAlmostZero M) :
    S.IsAlmostZero (P ⊗[V] M) := by
  refine isAlmostZero_iff.mpr fun ε hε t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul p x => rw [← tmul_smul, h.smul_eq_zero hε, tmul_zero]
  | add t t' ht ht' => rw [smul_add, ht, ht', add_zero]

variable {S} in
/-- The module of linear maps out of an almost zero module is almost zero. -/
theorem IsAlmostZero.linearMap_of_domain {M : Type*} [AddCommGroup M] [Module V M]
    (N : Type*) [AddCommGroup N] [Module V N] (h : S.IsAlmostZero M) :
    S.IsAlmostZero (M →ₗ[V] N) :=
  isAlmostZero_iff.mpr fun ε hε f ↦ LinearMap.ext fun x ↦ by
    rw [LinearMap.smul_apply, ← map_smul, h.smul_eq_zero hε, map_zero, LinearMap.zero_apply]

variable {S} in
/-- The module of linear maps into an almost zero module is almost zero. -/
theorem IsAlmostZero.linearMap_of_codomain (M : Type*) [AddCommGroup M] [Module V M]
    {N : Type*} [AddCommGroup N] [Module V N] (h : S.IsAlmostZero N) :
    S.IsAlmostZero (M →ₗ[V] N) :=
  isAlmostZero_iff.mpr fun ε hε f ↦ LinearMap.ext fun x ↦ by
    rw [LinearMap.smul_apply, h.smul_eq_zero hε, LinearMap.zero_apply]

/-- If `m ⊗[V] N` is killed by `m` then it vanishes: every element of `m` is a sum of products
of two elements of `m`. -/
private theorem subsingleton_ideal_tensor_of_isAlmostZero (N : Type*) [AddCommGroup N]
    [Module V N] (h : S.IsAlmostZero (S.ideal ⊗[V] N)) : Subsingleton (S.ideal ⊗[V] N) := by
  have hzero : S.tildeToIdeal.rTensor N = 0 := by
    refine TensorProduct.ext' fun t x ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have hab : S.tildeToIdeal (a ⊗ₜ b) = (a : V) • b := Subtype.ext (by simp)
      rw [LinearMap.rTensor_tmul, hab, ← smul_tmul', h.smul_eq_zero a.2, LinearMap.zero_apply]
    | add t t' ht ht' => simp_all [add_tmul]
  refine ⟨fun y y' ↦ ?_⟩
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective N S.tildeToIdeal_surjective y
  obtain ⟨y', rfl⟩ := LinearMap.rTensor_surjective N S.tildeToIdeal_surjective y'
  rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]

/-- A module `M` is almost zero iff `m ⊗[V] M = 0` (Gabber–Ramero Remark 2.1.4(i)). -/
theorem isAlmostZero_iff_subsingleton_ideal_tensor (M : Type*) [AddCommGroup M] [Module V M] :
    S.IsAlmostZero M ↔ Subsingleton (S.ideal ⊗[V] M) := by
  refine ⟨fun h ↦ S.subsingleton_ideal_tensor_of_isAlmostZero M (h.tensorProduct _),
    fun h ↦ isAlmostZero_iff.mpr fun ε hε x ↦ ?_⟩
  have := congrArg ((TensorProduct.lid V M).toLinearMap ∘ₗ S.ideal.subtype.rTensor M)
    (Subsingleton.elim ((⟨ε, hε⟩ : S.ideal) ⊗ₜ[V] x) 0)
  simpa using this

/-- A module `M` is almost zero iff `m~ ⊗[V] M = 0` (Gabber–Ramero Remark 2.1.4(i)). -/
theorem isAlmostZero_iff_subsingleton_tilde_tensor (M : Type*) [AddCommGroup M] [Module V M] :
    S.IsAlmostZero M ↔ Subsingleton (S.tilde ⊗[V] M) := by
  rw [(TensorProduct.assoc V S.ideal S.ideal M).toEquiv.subsingleton_congr,
    ← isAlmostZero_iff_subsingleton_ideal_tensor]
  refine ⟨fun h ↦ h.tensorProduct _, fun h ↦ ?_⟩
  have := S.subsingleton_ideal_tensor_of_isAlmostZero M h
  exact (S.isAlmostZero_iff_subsingleton_ideal_tensor M).mpr this

/-- The almost zero `V`-modules, as an object property of `ModuleCat V`. -/
def almostZero : CategoryTheory.ObjectProperty (ModuleCat.{v} V) := fun M ↦ S.IsAlmostZero M

@[simp]
theorem almostZero_iff (M : ModuleCat.{v} V) : S.almostZero M ↔ S.IsAlmostZero M :=
  Iff.rfl

instance : S.almostZero.IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ (e.toLinearEquiv.isAlmostZero_iff S).mp h⟩

/-! ### Almost isomorphisms -/

/-- A linear map is an *almost isomorphism* if its kernel and its cokernel are almost zero
(Gabber–Ramero (2.1.3)). -/
def IsAlmostIso {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]
    (f : M →ₗ[V] N) : Prop :=
  S.IsAlmostZero (LinearMap.ker f) ∧ S.IsAlmostZero (N ⧸ LinearMap.range f)

section IsAlmostIso

variable {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

variable {S} in
theorem isAlmostIso_iff {f : M →ₗ[V] N} :
    S.IsAlmostIso f ↔ S.IsAlmostZero (LinearMap.ker f) ∧ S.IsAlmostZero (N ⧸ LinearMap.range f) :=
  Iff.rfl

/-- A bijective linear map is an almost isomorphism for every basic setup. -/
theorem isAlmostIso_of_bijective {f : M →ₗ[V] N} (hf : Function.Bijective f) : S.IsAlmostIso f := by
  have : Subsingleton (LinearMap.ker f) := by
    rw [Submodule.subsingleton_iff_eq_bot]; exact LinearMap.ker_eq_bot.mpr hf.1
  have : Subsingleton (N ⧸ LinearMap.range f) := by
    rw [Submodule.Quotient.subsingleton_iff]; exact LinearMap.range_eq_top.mpr hf.2
  exact ⟨S.isAlmostZero_of_subsingleton, S.isAlmostZero_of_subsingleton⟩

/-- The inclusion `m → V` is an almost isomorphism, although it is not surjective unless
`m = V`. -/
@[simp]
theorem isAlmostIso_subtype : S.IsAlmostIso S.ideal.subtype := by
  have : Subsingleton (LinearMap.ker S.ideal.subtype) := by
    rw [Submodule.ker_subtype]; infer_instance
  rw [isAlmostIso_iff, Submodule.range_subtype]
  exact ⟨S.isAlmostZero_of_subsingleton, S.isAlmostZero_quotient⟩

end IsAlmostIso

/-! ### The classical and the zero setups -/

/-- For `m = V`, the module `m~ = V ⊗[V] V` is flat. -/
theorem flat_tilde_top : Module.Flat V ((⊤ : Ideal V) ⊗[V] (⊤ : Ideal V)) :=
  .of_linearEquiv (LinearEquiv.ofBijective _ Submodule.mulMap_top_top_bijective)

variable (V) in
/-- The classical setup `(V, V)`, for which almost mathematics is ordinary commutative algebra
(Gabber–Ramero Example 2.1.2(ii)). -/
def classical : BasicSetup V where
  ideal := ⊤
  isIdempotentElem := Ideal.top_mul ⊤
  flat_tilde := flat_tilde_top

@[simp]
theorem classical_ideal : (classical V).ideal = ⊤ :=
  (rfl)

variable (V) in
/-- The zero setup `(V, 0)`: the zero ideal is idempotent and `m~ = 0` is flat. Every module is
almost zero for it. -/
def zero : BasicSetup V where
  ideal := ⊥
  isIdempotentElem := Ideal.bot_mul ⊥
  flat_tilde := inferInstance

@[simp]
theorem zero_ideal : (zero V).ideal = ⊥ :=
  (rfl)

/-- For the classical setup, the multiplication map `m~ → m` is bijective. -/
theorem classical_tildeToIdeal_bijective : Function.Bijective (classical V).tildeToIdeal :=
  -- `(classical V).tildeMul` is `Submodule.mulMap ⊤ ⊤`, and `coe_tildeToIdeal` holds by `rfl`.
  ⟨fun _ _ hst ↦ Submodule.mulMap_top_top_bijective.1 (congrArg Subtype.val hst),
    (classical V).tildeToIdeal_surjective⟩

/-- The ideal of the zero setup is zero; hence `(zero V).tilde` is zero as well. -/
instance : Subsingleton (zero V).ideal :=
  Submodule.subsingleton_iff_eq_bot.mpr zero_ideal

/-- For the zero setup, `m~ = 0`, so the multiplication map `m~ → V` is zero. -/
@[simp]
theorem zero_tildeMul : (zero V).tildeMul = 0 :=
  Subsingleton.elim _ _

section ClassicalZero

variable {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- For the classical setup, almost zero means zero. -/
@[simp]
theorem isAlmostZero_classical_iff : (classical V).IsAlmostZero M ↔ Subsingleton M := by
  refine ⟨fun h ↦ ⟨fun x y ↦ ?_⟩, fun _ ↦ isAlmostZero_of_subsingleton _⟩
  rw [← one_smul V x, ← one_smul V y, h.smul_eq_zero (by simp), h.smul_eq_zero (by simp)]

/-- For the classical setup, an almost isomorphism is a bijective linear map. -/
@[simp]
theorem isAlmostIso_classical_iff {f : M →ₗ[V] N} :
    (classical V).IsAlmostIso f ↔ Function.Bijective f := by
  simp only [isAlmostIso_iff, isAlmostZero_classical_iff, Submodule.subsingleton_iff_eq_bot,
    Submodule.Quotient.subsingleton_iff, LinearMap.ker_eq_bot, LinearMap.range_eq_top,
    Function.Bijective]

/-- For the zero setup, every module is almost zero. -/
@[simp]
theorem isAlmostZero_zero : (zero V).IsAlmostZero M :=
  isAlmostZero_iff.mpr fun ε hε x ↦ by
    rw [zero_ideal, Ideal.mem_bot] at hε
    rw [hε, zero_smul]

/-- For the zero setup, every linear map is an almost isomorphism. -/
@[simp]
theorem isAlmostIso_zero (f : M →ₗ[V] N) : (zero V).IsAlmostIso f :=
  ⟨isAlmostZero_zero, isAlmostZero_zero⟩

end ClassicalZero

/-! ### Conditions (A) and (B) -/

/-- Condition (A) of Gabber–Ramero (2.1.6): any two elements of `m` have a common divisor in `m`,
so that `m` is the directed union of the principal ideals generated by its elements. -/
def IsFilteredPrincipal : Prop :=
  ∀ x ∈ S.ideal, ∀ y ∈ S.ideal, ∃ z ∈ S.ideal, z ∣ x ∧ z ∣ y

/-- Condition (B) of Gabber–Ramero (2.1.6): for every `k ≥ 1`, the `k`-th powers of elements of
`m` generate `m`. -/
def PowersGenerate : Prop :=
  ∀ k : ℕ, 0 < k → Ideal.span ((fun x : V ↦ x ^ k) '' (S.ideal : Set V)) = S.ideal

variable {S}

theorem isFilteredPrincipal_iff :
    S.IsFilteredPrincipal ↔ ∀ x ∈ S.ideal, ∀ y ∈ S.ideal, ∃ z ∈ S.ideal, z ∣ x ∧ z ∣ y :=
  Iff.rfl

theorem powersGenerate_iff :
    S.PowersGenerate ↔
      ∀ k : ℕ, 0 < k → Ideal.span ((fun x : V ↦ x ^ k) '' (S.ideal : Set V)) = S.ideal :=
  Iff.rfl

/-- If any two elements of an ideal `I` have a common divisor in `I`, as for the ideal of a basic
setup satisfying condition (A), then every element of `I ^ k` is divisible by the `k`-th power of
a single element of `I`. -/
theorem exists_pow_dvd_of_mem_pow {I : Ideal V} (h : ∀ x ∈ I, ∀ y ∈ I, ∃ z ∈ I, z ∣ x ∧ z ∣ y) :
    ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ z ∈ I, z ^ k ∣ x
  | 0, x, _ => ⟨0, I.zero_mem, by simp⟩
  | k + 1, x, hx => by
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) fun x y hx hy ↦ ?_
    · obtain ⟨z', hz', hz'b⟩ := exists_pow_dvd_of_mem_pow h k b hb
      obtain ⟨z, hz, hza, hzz'⟩ := h a ha z' hz'
      exact ⟨z, hz, pow_succ' z k ▸ mul_dvd_mul hza ((pow_dvd_pow_of_dvd hzz' k).trans hz'b)⟩
    · obtain ⟨z₁, hz₁, hz₁x⟩ := hx
      obtain ⟨z₂, hz₂, hz₂y⟩ := hy
      obtain ⟨z, hz, hzz₁, hzz₂⟩ := h z₁ hz₁ z₂ hz₂
      exact ⟨z, hz, dvd_add ((pow_dvd_pow_of_dvd hzz₁ _).trans hz₁x)
        ((pow_dvd_pow_of_dvd hzz₂ _).trans hz₂y)⟩

/-- Condition (A) implies condition (B) for the idempotent ideal of a basic setup
(Gabber–Ramero (2.1.6)): an element of `m = m ^ k` is divisible by `z ^ k` for some `z ∈ m`. -/
theorem IsFilteredPrincipal.powersGenerate (h : S.IsFilteredPrincipal) : S.PowersGenerate := by
  intro k hk
  refine le_antisymm (Ideal.span_le.mpr ?_) fun x hx ↦ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact S.ideal.pow_mem_of_mem hy k hk
  · rw [← S.isIdempotentElem.pow_eq hk.ne'] at hx
    obtain ⟨z, hz, hzx⟩ := exists_pow_dvd_of_mem_pow (isFilteredPrincipal_iff.mp h) k x hx
    exact Ideal.mem_of_dvd _ hzx (Ideal.subset_span ⟨z, hz, rfl⟩)

/-! ### Condition (A) and flatness of `m~` -/

section FilteredPrincipal

variable {I : Ideal V}

/-- A divisibility in `V` between two elements of `I` is a membership in a cyclic submodule
of `I`. -/
private theorem mem_span_singleton_of_dvd {x z : I} (h : (z : V) ∣ x) : x ∈ V ∙ z := by
  obtain ⟨c, hc⟩ := h
  exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext (by simp [hc, mul_comm])⟩

variable (hI : ∀ x ∈ I, ∀ y ∈ I, ∃ z ∈ I, z ∣ x ∧ z ∣ y)
include hI

/-- Under condition (A), two elements of `I` lie in a common cyclic submodule of `I`. -/
private theorem exists_mem_span_singleton (x y : I) : ∃ z : I, x ∈ V ∙ z ∧ y ∈ V ∙ z := by
  obtain ⟨z, hz, hx, hy⟩ := hI x x.2 y y.2
  exact ⟨⟨z, hz⟩, mem_span_singleton_of_dvd hx, mem_span_singleton_of_dvd hy⟩

/-- Under condition (A), every finitely generated submodule of `I` lies in a cyclic one. -/
private theorem exists_le_span_singleton {Q : Submodule V I} (hQ : Q.FG) :
    ∃ z : I, Q ≤ V ∙ z := by
  classical
  obtain ⟨s, rfl⟩ := hQ
  suffices ∃ z : I, ∀ x ∈ s, x ∈ V ∙ z from
    this.imp fun z hz ↦ Submodule.span_le.mpr hz
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨z₁, hz₁⟩ := ih
    obtain ⟨z, ha, h₁⟩ := exists_mem_span_singleton hI a z₁
    refine ⟨z, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact Submodule.span_singleton_le_iff_mem _ _ |>.mpr h₁ (hz₁ x hx)

/-- Under condition (A), a tensor that vanishes in `I ⊗[V] N` and comes from a finitely
generated submodule of `I` already vanishes in `(V ∙ z) ⊗[V] N` for some `z ∈ I`. -/
private theorem exists_rTensor_inclusion_eq_zero (N : Type*) [AddCommGroup N] [Module V N]
    {P : Submodule V I} (hP : P.FG) {t : P ⊗[V] N} (ht : P.subtype.rTensor N t = 0) :
    ∃ (z : I) (h : P ≤ V ∙ z), (Submodule.inclusion h).rTensor N t = 0 := by
  obtain ⟨Q, hPQ, hQ, hQt⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hP ht
  obtain ⟨z, hz⟩ := exists_le_span_singleton hI hQ
  have : Submodule.inclusion (hPQ.trans hz) =
      Submodule.inclusion hz ∘ₗ Submodule.inclusion hPQ := by
    ext; simp
  exact ⟨z, hPQ.trans hz, by rw [this, LinearMap.rTensor_comp_apply, hQt, map_zero]⟩

omit hI in
/-- The bilinear map `(V ∙ z) × (V ∙ z) → I`, `(c • z, t) ↦ c • t`, well defined because the
annihilator of `z` kills `V ∙ z`. -/
private noncomputable def spanSingletonMul (z : I) : (V ∙ z) →ₗ[V] (V ∙ z) →ₗ[V] I :=
  (Ideal.torsionOf V I z).liftQ ((LinearMap.lsmul V I).compl₂ (V ∙ z).subtype)
      (fun u hu ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun t ↦ by
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp t.2
        rw [Ideal.mem_torsionOf_iff] at hu
        simp [← hd, hu]) ∘ₗ
    (Ideal.quotTorsionOfEquivSpanSingleton V I z).symm.toLinearMap

omit hI in
private theorem spanSingletonMul_apply {z : I} {c : V} {s : V ∙ z} (hs : (s : I) = c • z)
    (t : V ∙ z) : spanSingletonMul z s t = c • (t : I) := by
  have : (Ideal.quotTorsionOfEquivSpanSingleton V I z).symm s = Submodule.Quotient.mk c := by
    rw [LinearEquiv.symm_apply_eq, Ideal.quotTorsionOfEquivSpanSingleton_apply_mk]
    exact Subtype.ext (by simp [hs])
  simp only [spanSingletonMul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    Submodule.liftQ_apply, LinearMap.compl₂_apply, LinearMap.lsmul_apply, Submodule.subtype_apply]

/-- Under condition (A), if `a • (x ⊗ x) = 0` in `I ⊗[V] I` then `x = c • z` for some `z ∈ I`
with `a * c * c * z = 0`: the vanishing already happens in `(V ∙ z) ⊗[V] (V ∙ z) ≅ V ∙ z`. -/
private theorem exists_eq_smul_and_mul_eq_zero {x : I} {a : V}
    (h : a • (x ⊗ₜ[V] x) = 0) : ∃ (z : I) (c : V), x = c • z ∧ a * c * c * z = 0 := by
  let x₀ : V ∙ x := ⟨x, Submodule.mem_span_singleton_self x⟩
  -- Make the left factor cyclic: the vanishing holds in `(V ∙ z₁) ⊗[V] I`.
  obtain ⟨z₁, h₁, ht₁⟩ := exists_rTensor_inclusion_eq_zero hI I (Submodule.fg_span_singleton x)
    (t := a • (x₀ ⊗ₜ x)) (by simpa [x₀] using h)
  let x₁ : V ∙ z₁ := Submodule.inclusion h₁ x₀
  -- Swap the factors and make the other factor cyclic as well, containing the first one.
  obtain ⟨z, h, ht⟩ := exists_rTensor_inclusion_eq_zero hI (V ∙ z₁)
    (Submodule.fg_span_singleton z₁) (t := a • (x₁ ⊗ₜ x₁)) (by
      simpa [x₁] using congrArg (TensorProduct.comm V (V ∙ z₁) I) ht₁)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h (h₁ x₀.2))
  have hxz : c * (z : V) = x := by simpa [x₀] using congrArg Subtype.val hc
  refine ⟨z, c, by simpa [x₀] using hc.symm, ?_⟩
  -- Apply the identification `(V ∙ z) ⊗[V] (V ∙ z) ≅ V ∙ z`.
  have := congrArg (TensorProduct.lift (spanSingletonMul z) ∘ₗ
    (Submodule.inclusion h).lTensor (V ∙ z)) ht
  simp only [map_smul, LinearMap.rTensor_tmul,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.lift.tmul,
    map_zero] at this
  rw [spanSingletonMul_apply (c := c) (by simp [x₁, x₀, hc])] at this
  have := congrArg (Subtype.val : I → V) this
  simp only [Submodule.coe_smul, Submodule.coe_inclusion, x₁, x₀, smul_eq_mul,
    ZeroMemClass.coe_zero] at this
  linear_combination this + a * c * hxz

/-- Under condition (A), finitely many elements of `I ⊗[V] I` are multiples of a single
`z ⊗ z` with `z ∈ I`. -/
private theorem exists_forall_mem_span_tmul_self (s : Finset (I ⊗[V] I)) :
    ∃ z : I, ∀ t ∈ s, t ∈ V ∙ (z ⊗ₜ[V] z) := by
  classical
  have hmono {z z' : I} (hz : z ∈ V ∙ z') : V ∙ (z ⊗ₜ[V] z) ≤ V ∙ (z' ⊗ₜ[V] z') := by
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [Submodule.span_singleton_le_iff_mem, smul_tmul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hone (t : I ⊗[V] I) : ∃ z : I, t ∈ V ∙ (z ⊗ₜ[V] z) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨z, hx, hy⟩ := exists_mem_span_singleton hI x y
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [smul_tmul_smul]
      exact ⟨z, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
    | add t t' ht ht' =>
      obtain ⟨z₁, hz₁⟩ := ht
      obtain ⟨z₂, hz₂⟩ := ht'
      obtain ⟨z, h₁, h₂⟩ := exists_mem_span_singleton hI z₁ z₂
      exact ⟨z, add_mem (hmono h₁ hz₁) (hmono h₂ hz₂)⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert t s _ ih =>
    obtain ⟨z₁, hz₁⟩ := ih
    obtain ⟨z₂, hz₂⟩ := hone t
    obtain ⟨z, h₁, h₂⟩ := exists_mem_span_singleton hI z₁ z₂
    refine ⟨z, fun t' ht' ↦ ?_⟩
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact hmono h₂ hz₂
    · exact hmono h₁ (hz₁ t' ht')

/-- **Condition (A) makes `m~` flat** (Gabber–Ramero (2.1.6) and Proposition 2.1.7(i)): if `I` is
an idempotent ideal any two of whose elements have a common divisor in `I`, so that `I` is the
directed union of the principal ideals generated by its elements, then `I ⊗[V] I` is a flat
`V`-module. No element of `I` needs to be a nonzerodivisor. -/
theorem flat_tilde_of_isFilteredPrincipal (hIdem : IsIdempotentElem I) :
    Module.Flat V (I ⊗[V] I) := by
  classical
  refine Module.Flat.of_forall_isTrivialRelation fun {l f t} hft ↦ ?_
  -- All the `t i` are multiples `c i • (z ⊗ z)` of a single `z ⊗ z`.
  obtain ⟨z, hz⟩ := exists_forall_mem_span_tmul_self hI (Finset.univ.image t)
  choose c hc using fun i ↦ Submodule.mem_span_singleton.mp
    (hz (t i) (Finset.mem_image_of_mem t (Finset.mem_univ i)))
  have ha : (∑ i, f i * c i) • (z ⊗ₜ[V] z) = 0 := by
    simpa [Finset.sum_smul, ← hc, smul_smul] using hft
  -- Write `z = c' • w` with `a * c' * c' * w = 0`, and `w = y ^ 2 * d` with `y ∈ I`.
  obtain ⟨w, c', hzw, hw⟩ := exists_eq_smul_and_mul_eq_zero hI ha
  obtain ⟨y, hy, d, hd⟩ := exists_pow_dvd_of_mem_pow hI 2 w
    (by rw [hIdem.pow_eq two_ne_zero]; exact w.2)
  have hzy : z = (c' * y * d) • (⟨y, hy⟩ : I) := by
    rw [hzw]
    ext
    simp only [Submodule.coe_smul, smul_eq_mul, hd]
    ring
  refine ⟨1, fun i _ ↦ c i * (c' * y * d) ^ 2, fun _ ↦ ⟨y, hy⟩ ⊗ₜ[V] ⟨y, hy⟩, fun i ↦ ?_,
    fun _ ↦ ?_⟩
  · rw [← hc i, hzy, smul_tmul_smul, Fin.sum_univ_one, smul_smul, sq]
  · rw [Finset.sum_congr rfl fun i _ ↦ (mul_assoc (f i) (c i) _).symm, ← Finset.sum_mul]
    linear_combination (d : V) * hw - (∑ i, f i * c i) * c' ^ 2 * d * hd

end FilteredPrincipal

end BasicSetup

end TauCeti.Almost
