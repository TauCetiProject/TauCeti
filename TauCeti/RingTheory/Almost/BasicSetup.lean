/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Torsion

/-!
# Basic setups of almost mathematics

A *basic setup* `(V, m)` consists of a commutative ring `V` and an ideal `m` such that
`m * m = m` and `m~ := m ⊗_V m` is a flat `V`-module. Almost mathematics over `(V, m)` neglects
the `V`-modules killed by `m`: a `V`-module `M` is *almost zero* if `m • M = 0`, and a linear map
is an *almost isomorphism* if its kernel and cokernel are almost zero. Idempotence of `m` is what
makes almost zero modules closed under extensions, and flatness of `m~` is what makes
`M ↦ m~ ⊗_V M` exact; here we show that this functor detects almost zero modules.

A basic setup is data rather than a type class, because one ring carries several setups (for a
perfectoid ring, the setup of topologically nilpotent elements and the root setup of a
pseudouniformizer). The classical setup `(V, V)` recovers ordinary commutative algebra, and the
zero setup `(V, 0)` makes every module almost zero.

## Main definitions

* `TauCeti.Almost.BasicSetup`: an idempotent ideal `m` with flat `m ⊗_V m`.
* `TauCeti.Almost.BasicSetup.tilde`: the `V`-module `m~ = m ⊗_V m`, and
  `TauCeti.Almost.BasicSetup.tildeToIdeal`: the multiplication `m~ → m`, which is surjective.
* `TauCeti.Almost.BasicSetup.IsAlmostZero`, `TauCeti.Almost.BasicSetup.almostZero`: modules
  killed by `m`, as a predicate and as an object property of `ModuleCat V`.
* `TauCeti.Almost.BasicSetup.IsAlmostIso`: linear maps with almost zero kernel and cokernel.
* `TauCeti.Almost.BasicSetup.classical`, `TauCeti.Almost.BasicSetup.zero`: the setups
  `(V, V)` and `(V, 0)`.
* `TauCeti.Almost.BasicSetup.baseChange`: the setup `(W, mW)` for a `V`-algebra `W`, and
  `TauCeti.Almost.BasicSetup.baseChangeTildeEquiv`: the isomorphism `W ⊗_V m~ ≅ mW ⊗_W mW`.
* `TauCeti.Almost.BasicSetup.IsFilteredPrincipal`, `TauCeti.Almost.BasicSetup.PowersGenerate`:
  Gabber–Ramero's conditions (A) and (B).

## Main results

* `TauCeti.Almost.BasicSetup.isAlmostZero_iff_subsingleton_tilde_tensor`: `M` is almost zero
  iff `m~ ⊗_V M = 0`; likewise with `m ⊗_V M`.
* `TauCeti.Almost.BasicSetup.flat_tilde_map`: `mW ⊗_W mW ≅ W ⊗_V m~` is flat, so basic setups
  base change.
* `TauCeti.Almost.BasicSetup.isAlmostZero_classical_iff`,
  `TauCeti.Almost.BasicSetup.isAlmostIso_classical_iff`: classically, almost zero means zero and
  almost isomorphisms are bijections.
* `TauCeti.Almost.BasicSetup.IsFilteredPrincipal.powersGenerate`: condition (A) implies
  condition (B).
* `TauCeti.Almost.BasicSetup.baseChange_away_eq_classical`: inverting an element of `m` makes the
  setup classical.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Math. 1800, Springer (2003),
  §2.1: (2.1.1), Example 2.1.2, (2.1.3), Remark 2.1.4 and (2.1.6).
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1.
-/

public section

open scoped TensorProduct Pointwise

universe u w

namespace TauCeti.Almost

/-- A *basic setup* `(V, m)`: an ideal `m` of `V` with `m * m = m` such that `m~ = m ⊗_V m` is a
flat `V`-module (Gabber–Ramero (2.1.1) and the standing assumption of (2.5.14)). It is data rather
than a class, since one ring carries several setups. -/
@[ext]
structure BasicSetup (V : Type u) [CommRing V] where
  /-- The ideal `m`. -/
  ideal : Ideal V
  /-- `m * m = m`, in the semiring `Ideal V`. -/
  isIdempotentElem : IsIdempotentElem ideal
  /-- `m~ = m ⊗_V m` is a flat `V`-module. -/
  flat_tilde : Module.Flat V (ideal ⊗[V] ideal)

namespace BasicSetup

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-! ### The module `m~` -/

/-- The `V`-module `m~ := m ⊗_V m` of a basic setup (Gabber–Ramero (2.1.1)). -/
abbrev tilde : Type u := S.ideal ⊗[V] S.ideal

instance : Module.Flat V S.tilde := S.flat_tilde

/-- The multiplication `m~ → m`, `x ⊗ y ↦ x * y` (Gabber–Ramero (2.1.1)); it is surjective because
`m * m = m`. Composed with `m ↪ V` it is Mathlib's `Submodule.mulMap`. -/
noncomputable def tildeToIdeal : S.tilde →ₗ[V] S.ideal :=
  (LinearEquiv.ofEq _ _ S.isIdempotentElem.eq).toLinearMap ∘ₗ Submodule.mulMap' S.ideal S.ideal

@[simp]
theorem coe_tildeToIdeal_tmul (a b : S.ideal) :
    (S.tildeToIdeal (a ⊗ₜ b) : V) = a * b :=
  (rfl)

theorem subtype_comp_tildeToIdeal :
    S.ideal.subtype ∘ₗ S.tildeToIdeal = Submodule.mulMap S.ideal S.ideal :=
  TensorProduct.ext' fun _ _ ↦ rfl

theorem tildeToIdeal_surjective : Function.Surjective S.tildeToIdeal := by
  rw [tildeToIdeal, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (LinearEquiv.surjective _).comp (Submodule.mulMap'_surjective _ _)

/-- In a basic setup, `m • m = m`: every element of `m` is a sum of products of two elements of
`m`. -/
theorem ideal_smul_top_eq_top : S.ideal • (⊤ : Submodule V S.ideal) = ⊤ := by
  apply Submodule.map_injective_of_injective S.ideal.injective_subtype
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Ideal.smul_eq_mul,
    S.isIdempotentElem.eq]

/-! ### Almost zero modules and almost isomorphisms -/

section AlmostZero

variable (M : Type*) [AddCommGroup M] [Module V M]

/-- A `V`-module `M` is *almost zero* for the basic setup `(V, m)` if `m • M = 0`
(Gabber–Ramero (2.1.3)). -/
def IsAlmostZero : Prop :=
  Module.IsTorsionBySet V M S.ideal

variable {S M}

theorem isAlmostZero_iff : S.IsAlmostZero M ↔ ∀ ε ∈ S.ideal, ∀ x : M, ε • x = 0 :=
  ⟨fun h ε hε x ↦ h (x := x) (a := ⟨ε, hε⟩), fun h x a ↦ h a a.2 x⟩

theorem isAlmostZero_iff_le_annihilator : S.IsAlmostZero M ↔ S.ideal ≤ Module.annihilator V M :=
  Module.isTorsionBySet_iff_subset_annihilator V M

theorem IsAlmostZero.smul_eq_zero (h : S.IsAlmostZero M) {ε : V} (hε : ε ∈ S.ideal) (x : M) :
    ε • x = 0 :=
  isAlmostZero_iff.mp h ε hε x

variable (S M)

theorem isAlmostZero_of_subsingleton [Subsingleton M] : S.IsAlmostZero M :=
  fun _ _ ↦ Subsingleton.elim _ _

/-- The quotient `M / m • M` is almost zero. -/
theorem isAlmostZero_quotient_smul_top : S.IsAlmostZero (M ⧸ S.ideal • (⊤ : Submodule V M)) :=
  Module.isTorsionBySet_quotient_ideal_smul M S.ideal

/-- The quotient `V / m` is almost zero. -/
theorem isAlmostZero_quotient : S.IsAlmostZero (V ⧸ S.ideal) :=
  (Module.isTorsionBySet_quotient_iff _ _).mpr fun x _ hε ↦ S.ideal.mul_mem_right x hε

/-- Almost zero modules are detected by `m ⊗_V -` (Gabber–Ramero Remark 2.1.4(i)). -/
theorem isAlmostZero_iff_subsingleton_ideal_tensor :
    S.IsAlmostZero M ↔ Subsingleton (S.ideal ⊗[V] M) := by
  refine ⟨fun h ↦ subsingleton_tensorProduct_of_isTorsionBySet_right S.ideal_smul_top_eq_top h,
    fun h ↦ isAlmostZero_iff.mpr fun ε hε x ↦ ?_⟩
  have := congrArg ((TensorProduct.lid V M).toLinearMap ∘ₗ (S.ideal.subtype.rTensor M))
    (Subsingleton.elim (⟨ε, hε⟩ ⊗ₜ[V] x) 0)
  simpa using this

/-- Almost zero modules are detected by `m~ ⊗_V -` (Gabber–Ramero Remark 2.1.4(i)). -/
theorem isAlmostZero_iff_subsingleton_tilde_tensor :
    S.IsAlmostZero M ↔ Subsingleton (S.tilde ⊗[V] M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ isAlmostZero_iff.mpr fun ε hε x ↦ ?_⟩
  · have := (isAlmostZero_iff_subsingleton_ideal_tensor S M).mp h
    have := (isAlmostZero_iff_subsingleton_ideal_tensor S (S.ideal ⊗[V] M)).mp
      (S.isAlmostZero_of_subsingleton _)
    exact (TensorProduct.assoc V S.ideal S.ideal M).toEquiv.subsingleton
  · rw [← S.isIdempotentElem.eq] at hε
    refine Submodule.mul_induction_on (C := fun ε ↦ ε • x = 0) hε (fun a ha b hb ↦ ?_)
      fun _ _ h₁ h₂ ↦ by rw [add_smul, h₁, h₂, add_zero]
    have := congrArg
      ((TensorProduct.lid V M).toLinearMap ∘ₗ (Submodule.mulMap S.ideal S.ideal).rTensor M)
      (Subsingleton.elim ((⟨a, ha⟩ ⊗ₜ[V] ⟨b, hb⟩) ⊗ₜ[V] x) 0)
    simpa using this

end AlmostZero

/-- The almost zero `V`-modules, as an object property of `ModuleCat V`
(Gabber–Ramero (2.2.2)). -/
def almostZero : CategoryTheory.ObjectProperty (ModuleCat.{w} V) :=
  fun M ↦ S.IsAlmostZero M

variable {S} in
theorem almostZero_iff (M : ModuleCat.{w} V) : S.almostZero M ↔ S.IsAlmostZero M :=
  Iff.rfl

instance : S.almostZero.IsClosedUnderIsomorphisms where
  of_iso e h := isAlmostZero_iff.mpr fun ε hε x ↦ by
    rw [← e.inv_hom_id_apply x, ← map_smul, h.smul_eq_zero hε, map_zero]

section AlmostIso

variable {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- A linear map is an *almost isomorphism* if its kernel and cokernel are almost zero
(Gabber–Ramero (2.1.3)). -/
def IsAlmostIso (f : M →ₗ[V] N) : Prop :=
  S.IsAlmostZero (LinearMap.ker f) ∧ S.IsAlmostZero (N ⧸ LinearMap.range f)

/-- A bijective linear map is an almost isomorphism. -/
theorem isAlmostIso_of_bijective {f : M →ₗ[V] N} (hf : Function.Bijective f) :
    S.IsAlmostIso f := by
  have : Subsingleton (LinearMap.ker f) := by
    rw [Submodule.subsingleton_iff_eq_bot]; exact LinearMap.ker_eq_bot.mpr hf.1
  have : Subsingleton (N ⧸ LinearMap.range f) := by
    rw [Submodule.Quotient.subsingleton_iff]; exact LinearMap.range_eq_top.mpr hf.2
  exact ⟨S.isAlmostZero_of_subsingleton _, S.isAlmostZero_of_subsingleton _⟩

/-- The inclusion `m ↪ V` is an almost isomorphism, though it is not surjective unless `m = V`. -/
theorem isAlmostIso_subtype : S.IsAlmostIso S.ideal.subtype := by
  have : Subsingleton (LinearMap.ker S.ideal.subtype) := by
    rw [Submodule.subsingleton_iff_eq_bot]; exact Submodule.ker_subtype _
  refine ⟨S.isAlmostZero_of_subsingleton _, ?_⟩
  rw [Submodule.range_subtype]
  exact S.isAlmostZero_quotient

end AlmostIso

/-! ### The classical and zero setups -/

/-- The classical setup `(V, V)`, in which almost mathematics is ordinary commutative algebra
(Gabber–Ramero Example 2.1.2(ii)). -/
def classical (V : Type u) [CommRing V] : BasicSetup V where
  ideal := ⊤
  isIdempotentElem := by simp [IsIdempotentElem]
  flat_tilde :=
    have : Module.Flat V (⊤ : Ideal V) := .of_linearEquiv (Submodule.topEquiv (R := V) (M := V))
    inferInstance

@[simp]
theorem classical_ideal : (classical V).ideal = ⊤ :=
  (rfl)

/-- The zero setup `(V, 0)`: `0` is idempotent and `0 ⊗ 0 = 0` is flat. Every module is almost
zero for it. -/
def zero (V : Type u) [CommRing V] : BasicSetup V where
  ideal := ⊥
  isIdempotentElem := by simp [IsIdempotentElem]
  flat_tilde := inferInstance

@[simp]
theorem zero_ideal : (zero V).ideal = ⊥ :=
  (rfl)

section Classical

variable {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- For the classical setup, almost zero means zero (Gabber–Ramero Example 2.1.2(ii)). -/
theorem isAlmostZero_classical_iff : (classical V).IsAlmostZero M ↔ Subsingleton M :=
  ⟨fun h ↦ ⟨fun x y ↦ by
    rw [← one_smul V x, ← one_smul V y, h.smul_eq_zero Submodule.mem_top,
      h.smul_eq_zero Submodule.mem_top]⟩, fun _ ↦ (classical V).isAlmostZero_of_subsingleton M⟩

/-- For the classical setup, almost isomorphisms are bijections. -/
theorem isAlmostIso_classical_iff {f : M →ₗ[V] N} :
    (classical V).IsAlmostIso f ↔ Function.Bijective f := by
  rw [IsAlmostIso, isAlmostZero_classical_iff, isAlmostZero_classical_iff,
    Submodule.subsingleton_iff_eq_bot, Submodule.Quotient.subsingleton_iff, LinearMap.ker_eq_bot,
    LinearMap.range_eq_top, Function.Bijective]

/-- For the zero setup, every module is almost zero. -/
theorem isAlmostZero_zero : (zero V).IsAlmostZero M :=
  isAlmostZero_iff.mpr fun ε hε x ↦ by rw [(Submodule.mem_bot V).mp hε, zero_smul]

/-- For the zero setup, every linear map is an almost isomorphism. -/
theorem isAlmostIso_zero (f : M →ₗ[V] N) : (zero V).IsAlmostIso f :=
  ⟨isAlmostZero_zero, isAlmostZero_zero⟩

end Classical

/-! ### Base change -/

section BaseChange

variable (W : Type*) [CommRing W] [Algebra V W]

/-- The extended ideal `mW` is idempotent (Gabber–Ramero Remark 2.1.4(ii)). -/
theorem isIdempotentElem_map : IsIdempotentElem (S.ideal.map (algebraMap V W)) := by
  rw [IsIdempotentElem, ← Ideal.map_mul, S.isIdempotentElem.eq]

/-- The surjection `W ⊗_V m → mW`. -/
private noncomputable abbrev baseChangeIdealMap :
    W ⊗[V] S.ideal →ₗ[W] S.ideal.map (algebraMap V W) :=
  (Algebra.idealMap W S.ideal).liftBaseChange W

private theorem baseChangeIdealMap_surjective : Function.Surjective (S.baseChangeIdealMap W) := by
  let J := S.ideal.map (algebraMap V W)
  have hle : J ≤ (LinearMap.range (S.baseChangeIdealMap W)).map J.subtype :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦
      ⟨⟨algebraMap V W a, Ideal.mem_map_of_mem _ ha⟩, ⟨1 ⊗ₜ ⟨a, ha⟩, by ext; simp⟩, rfl⟩
  intro y
  obtain ⟨z, hz, hzy⟩ := hle y.2
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, Subtype.ext hzy⟩

/-- The kernel of `W ⊗_V m → mW` is killed by `mW`. -/
private theorem isTorsionBySet_ker_baseChangeIdealMap :
    Module.IsTorsionBySet W (LinearMap.ker (S.baseChangeIdealMap W))
      (S.ideal.map (algebraMap V W)) := by
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
    Ideal.map_le_iff_le_comap]
  intro ε hε
  rw [Ideal.mem_comap, Module.mem_annihilator]
  rintro ⟨k, hk⟩
  -- `w ⊗ a ↦ w ⊗ (a ε) = (ε w) ⊗ a` factors multiplication by `ε` through `W ⊗_V m → mW`.
  have key : ∀ x : W ⊗[V] S.ideal, (S.baseChangeIdealMap W x : W) • (1 ⊗ₜ[V] ⟨ε, hε⟩) =
      algebraMap V W ε • x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul w a =>
      simp only [LinearMap.liftBaseChange_tmul, SetLike.val_smul, Algebra.idealMap_apply_coe,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [mul_comm, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul,
        TensorProduct.smul_tmul]
      congr 1
      ext; simp [mul_comm]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, add_smul, hx, hy, smul_add]
  apply Subtype.ext
  rw [Submodule.coe_smul, ← key, LinearMap.mem_ker.mp hk, Submodule.coe_zero, zero_smul,
    Submodule.coe_zero]

/-- `mW • (W ⊗_V m) = W ⊗_V m`. -/
private theorem smul_top_baseChange_eq_top :
    S.ideal.map (algebraMap V W) • (⊤ : Submodule W (W ⊗[V] S.ideal)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul w a =>
    have ha : a ∈ S.ideal • (⊤ : Submodule V S.ideal) := by
      rw [S.ideal_smul_top_eq_top]; exact Submodule.mem_top
    refine Submodule.smul_induction_on (p := fun a ↦ w ⊗ₜ[V] a ∈ _) ha (fun r hr y _ ↦ ?_)
      fun _ _ h₁ h₂ ↦ by rw [TensorProduct.tmul_add]; exact add_mem h₁ h₂
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  | add x y hx hy => exact add_mem hx hy

/-- `π ⊗ π : (W ⊗_V m) ⊗_W (W ⊗_V m) → mW ⊗_W mW` is bijective: its kernel is generated by
`ker π ⊗ (W ⊗_V m)` and `(W ⊗_V m) ⊗ ker π`, which vanish since `mW` kills `ker π` and
`mW • (W ⊗_V m) = W ⊗_V m`. -/
private theorem map_baseChangeIdealMap_bijective :
    Function.Bijective (TensorProduct.map (S.baseChangeIdealMap W) (S.baseChangeIdealMap W)) := by
  have hπ := S.baseChangeIdealMap_surjective W
  have hex := LinearMap.exact_subtype_ker_map (S.baseChangeIdealMap W)
  refine ⟨?_, TensorProduct.map_surjective hπ hπ⟩
  have := subsingleton_tensorProduct_of_isTorsionBySet_right (S.smul_top_baseChange_eq_top W)
    (S.isTorsionBySet_ker_baseChangeIdealMap W)
  have := subsingleton_tensorProduct_of_isTorsionBySet_left
    (S.isTorsionBySet_ker_baseChangeIdealMap W) (S.smul_top_baseChange_eq_top W)
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  have hx : x ∈ LinearMap.ker (TensorProduct.map (S.baseChangeIdealMap W)
      (S.baseChangeIdealMap W)) := hx
  -- The kernel types are given explicitly so that both exactness hypotheses unify.
  rw [TensorProduct.map_ker (M := LinearMap.ker (S.baseChangeIdealMap W))
    (M' := LinearMap.ker (S.baseChangeIdealMap W)) hex hπ hex hπ] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  rw [Subsingleton.elim y 0, Subsingleton.elim z 0, map_zero, map_zero, add_zero]

/-- The base change of `m~` is `m~` for the extended ideal:
`W ⊗_V (m ⊗_V m) ≅ mW ⊗_W mW` (Gabber–Ramero Remark 2.1.4(ii)). -/
noncomputable def baseChangeTildeEquiv :
    W ⊗[V] S.tilde ≃ₗ[W] S.ideal.map (algebraMap V W) ⊗[W] S.ideal.map (algebraMap V W) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange V W S.ideal S.ideal ≪≫ₗ
    LinearEquiv.ofBijective _ (S.map_baseChangeIdealMap_bijective W)

@[simp]
theorem baseChangeTildeEquiv_tmul (w : W) (a b : S.ideal) :
    S.baseChangeTildeEquiv W (w ⊗ₜ (a ⊗ₜ b)) =
      w • (Algebra.idealMap W S.ideal a ⊗ₜ[W] Algebra.idealMap W S.ideal b) := by
  simp [baseChangeTildeEquiv, TensorProduct.smul_tmul']

/-- `mW ⊗_W mW ≅ W ⊗_V m~` is flat (Gabber–Ramero Remark 2.1.4(ii)). -/
theorem flat_tilde_map :
    Module.Flat W (S.ideal.map (algebraMap V W) ⊗[W] S.ideal.map (algebraMap V W)) :=
  .of_linearEquiv (S.baseChangeTildeEquiv W).symm

/-- The base change `(W, mW)` of a basic setup along `V → W` (Gabber–Ramero Remark 2.1.4(ii)). -/
def baseChange : BasicSetup W where
  ideal := S.ideal.map (algebraMap V W)
  isIdempotentElem := S.isIdempotentElem_map W
  flat_tilde := S.flat_tilde_map W

@[simp]
theorem baseChange_ideal : (S.baseChange W).ideal = S.ideal.map (algebraMap V W) :=
  (rfl)

/-- Base change preserves the classical setup. -/
@[simp]
theorem baseChange_classical : (classical V).baseChange W = classical W := by
  ext1; exact Ideal.map_top _

/-- Base change to `V / m` gives the zero setup. -/
theorem baseChange_quotient_eq_zero : S.baseChange (V ⧸ S.ideal) = zero (V ⧸ S.ideal) := by
  ext1; exact Ideal.map_quotient_self S.ideal

/-- Inverting an element of `m` makes the setup classical (Gabber–Ramero Remark 2.1.4(ii)); this
includes `ε = 0`, where `V[1/ε] = 0`. -/
theorem baseChange_away_eq_classical {ε : V} (hε : ε ∈ S.ideal) :
    S.baseChange (Localization.Away ε) = classical (Localization.Away ε) := by
  ext1
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hε)
    (IsLocalization.Away.algebraMap_isUnit ε)

end BaseChange

/-! ### Conditions (A) and (B) -/

/-- Condition (A) of Gabber–Ramero (2.1.6): `m` is the directed union of its principal subideals,
that is, any two elements of `m` have a common divisor in `m`. -/
def IsFilteredPrincipal : Prop :=
  ∀ x ∈ S.ideal, ∀ y ∈ S.ideal, ∃ z ∈ S.ideal, z ∣ x ∧ z ∣ y

/-- Condition (B) of Gabber–Ramero (2.1.6): for every `k ≥ 1` the `k`-th powers of elements of
`m` generate `m`. -/
def PowersGenerate : Prop :=
  ∀ k : ℕ, 0 < k → Ideal.span ((· ^ k) '' (S.ideal : Set V)) = S.ideal

/-- Condition (A) implies condition (B) (Gabber–Ramero (2.1.6)): a product of `k` elements of
`m` has a common divisor `z ∈ m` of its factors, so it lies in `(z ^ k)`; idempotence gives
`m = m ^ k`. -/
theorem IsFilteredPrincipal.powersGenerate {S : BasicSetup V} (h : S.IsFilteredPrincipal) :
    S.PowersGenerate := by
  intro k hk
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact Ideal.pow_mem_of_mem _ hx _ hk
  -- `m ^ i` lies in the ideal generated by `i`-th powers, for every `i`.
  have key (i : ℕ) : S.ideal ^ i ≤ Ideal.span ((· ^ i) '' (S.ideal : Set V)) := by
    induction i with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      exact Ideal.subset_span ⟨0, S.ideal.zero_mem, pow_zero 0⟩
    | succ i ih =>
      rw [pow_succ', Submodule.mul_le]
      intro a ha b hb
      refine Submodule.span_induction (p := fun b _ ↦ a * b ∈ Ideal.span _) ?_ (by simp)
        (fun _ _ _ _ hx hy ↦ by rw [mul_add]; exact add_mem hx hy)
        (fun r x _ hx ↦ by rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx)
        (ih hb)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, ⟨a', rfl⟩, ⟨z', rfl⟩⟩ := h _ ha z hz
      rw [show w * a' * (w * z') ^ i = a' * z' ^ i * w ^ (i + 1) by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨w, hw, rfl⟩)
  simpa [S.isIdempotentElem.pow_eq hk.ne'] using key k

theorem isFilteredPrincipal_classical : (classical V).IsFilteredPrincipal :=
  fun _ _ _ _ ↦ ⟨1, by simp, one_dvd _, one_dvd _⟩

theorem isFilteredPrincipal_zero : (zero V).IsFilteredPrincipal := fun x hx y hy ↦ by
  rw [zero_ideal, Submodule.mem_bot] at hx hy
  exact ⟨0, by simp, by simp [hx], by simp [hy]⟩

theorem powersGenerate_classical : (classical V).PowersGenerate :=
  isFilteredPrincipal_classical.powersGenerate

theorem powersGenerate_zero : (zero V).PowersGenerate :=
  isFilteredPrincipal_zero.powersGenerate

/-! ### `m~` for the classical and zero setups -/

/-- Classically, `m~ = V ⊗_V V → V` is bijective. -/
theorem tildeToIdeal_bijective_classical : Function.Bijective (classical V).tildeToIdeal := by
  let e : (classical V).tilde ≃ₗ[V] (classical V).ideal :=
    TensorProduct.congr Submodule.topEquiv Submodule.topEquiv ≪≫ₗ TensorProduct.lid V V ≪≫ₗ
      Submodule.topEquiv.symm
  -- `(classical V).ideal` is `⊤` by definition, and both maps send `a ⊗ b` to `a * b`.
  have : (classical V).tildeToIdeal = e.toLinearMap :=
    TensorProduct.ext' fun _ _ ↦ rfl
  rw [this]
  exact e.bijective

instance : Subsingleton (zero V).ideal :=
  Submodule.subsingleton_iff_eq_bot.mpr zero_ideal

theorem tildeToIdeal_bijective_zero : Function.Bijective (zero V).tildeToIdeal :=
  ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end BasicSetup

/-! ### Examples -/

section Examples

open BasicSetup

-- Over `(ℤ, ℤ)`, multiplication `m~ → m` sends `2 ⊗ 3 + 5 ⊗ 7` to `41` and `1 ⊗ 1` to `1`.
example : ((classical ℤ).tildeToIdeal
    (⟨2, by simp⟩ ⊗ₜ ⟨3, by simp⟩ + ⟨5, by simp⟩ ⊗ₜ ⟨7, by simp⟩) : ℤ) = 41 := by
  simp only [map_add, Submodule.coe_add, coe_tildeToIdeal_tmul]
  norm_num

example : ((classical ℤ).tildeToIdeal (⟨1, by simp⟩ ⊗ₜ ⟨1, by simp⟩) : ℤ) = 1 := by
  simp

-- Over `(ℤ, ℤ)`, `m~` is free of rank one.
noncomputable example : (classical ℤ).tilde ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective _ tildeToIdeal_bijective_classical).trans
    (LinearEquiv.ofEq _ _ classical_ideal ≪≫ₗ Submodule.topEquiv)

-- For `m = 0`, `m~ = 0` and the multiplication `m~ → V` is zero.
example (V : Type*) [CommRing V] : Subsingleton (zero V).tilde := inferInstance

example (V : Type*) [CommRing V] : Submodule.mulMap (zero V).ideal (zero V).ideal = 0 :=
  LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

-- On the zero ring the classical and zero setups coincide; on a nonzero ring they differ.
example (V : Type*) [CommRing V] [Subsingleton V] : classical V = zero V := by
  ext1; exact Subsingleton.elim _ _

example (V : Type*) [CommRing V] [Nontrivial V] : classical V ≠ zero V := fun h ↦ by
  simpa using congrArg BasicSetup.ideal h

-- `V / m` and the zero module are almost zero; over `(ℤ, ℤ)` the module `ℤ` is not.
example (V : Type*) [CommRing V] (S : BasicSetup V) :
    S.almostZero (ModuleCat.of V (V ⧸ S.ideal)) :=
  S.isAlmostZero_quotient

example (V : Type*) [CommRing V] (S : BasicSetup V) : S.almostZero (ModuleCat.of V PUnit) :=
  S.isAlmostZero_of_subsingleton _

example : ¬ (classical ℤ).almostZero (ModuleCat.of ℤ ℤ) := fun h ↦ by
  rw [almostZero_iff, isAlmostZero_classical_iff] at h
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

-- Multiplication by `2` on `ℤ` is not an almost isomorphism for `(ℤ, ℤ)`.
example : ¬ (classical ℤ).IsAlmostIso ((2 : ℤ) • LinearMap.id (R := ℤ) (M := ℤ)) := fun h ↦ by
  obtain ⟨x, hx⟩ := (isAlmostIso_classical_iff.mp h).2 1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hx
  omega

-- `(2) ⊆ ℤ` satisfies the divisibility condition of (A), but it is not idempotent and the squares
-- of its elements generate `(4) ≠ (2)`: (A) implies (B) only for idempotent ideals.
example : ∀ x ∈ Ideal.span {(2 : ℤ)}, ∀ y ∈ Ideal.span {(2 : ℤ)},
    ∃ z ∈ Ideal.span {(2 : ℤ)}, z ∣ x ∧ z ∣ y := fun _ hx _ hy ↦
  ⟨2, Ideal.mem_span_singleton_self 2, Ideal.mem_span_singleton.mp hx,
    Ideal.mem_span_singleton.mp hy⟩

example : ¬ IsIdempotentElem (Ideal.span {(2 : ℤ)}) := fun h ↦ by
  have h2 : (2 : ℤ) ∈ (Ideal.span {2} * Ideal.span {2} : Ideal ℤ) := by
    rw [h.eq]; exact Ideal.mem_span_singleton_self 2
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at h2
  omega

example : Ideal.span ((· ^ 2) '' (Ideal.span {(2 : ℤ)} : Set ℤ)) ≠ Ideal.span {2} := fun h ↦ by
  have hle : Ideal.span ((· ^ 2) '' (Ideal.span {(2 : ℤ)} : Set ℤ)) ≤ Ideal.span {4} := by
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact Ideal.mem_span_singleton.mpr ⟨a ^ 2, by ring⟩
  have h2 := hle (h ▸ Ideal.mem_span_singleton_self (2 : ℤ))
  rw [Ideal.mem_span_singleton] at h2
  omega

end Examples

end TauCeti.Almost
