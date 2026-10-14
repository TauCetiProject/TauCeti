/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Exact.Hom

/-!
# Extending additive homomorphisms between groups killed by `n`

Two mechanisms make `Hom(-, W)` exact on additive commutative groups killed by a natural number
`n`, and both are recorded here as extension statements along an injective homomorphism
`f : A →+ B` with `B` killed by `n`.

For `n = p` prime, `B` is an `𝔽_p`-vector space through `AddCommGroup.zmodModule`, and every
additive homomorphism between two such groups is `𝔽_p`-linear. Since an injective linear map of
vector spaces has a linear left inverse, an injective additive homomorphism into a group killed by
`p` has an additive left inverse, and so an additive homomorphism out of its source, with values in
an **arbitrary** type `N` with addition and zero, extends along it. For an additive commutative
monoid `N`, this makes `Hom(-, N)` exact on the additive groups killed by `p`.
Primality is essential for this: with `p = 4`, the identity of `2ℤ/4ℤ ≅ ℤ/2ℤ` does not extend
along the inclusion `2ℤ/4ℤ ⊆ ℤ/4ℤ` to a homomorphism
`ℤ/4ℤ → ℤ/2ℤ`, since every such homomorphism kills `2ℤ/4ℤ`.

For arbitrary `n` the extension property holds for the targets `W` that are injective
`ℤ/nℤ`-modules, in the form of Baer's criterion `Module.Baer (ZMod n) W`: an additive homomorphism
`A →+ W` between `ℤ/nℤ`-modules is linear, and `Module.Baer.extension_property` extends it along
`f`. The case `n = 0` is the extension property of a divisible group, and for `n ≠ 0` the target
`W = ℤ/nℤ` is covered by `Module.Baer.zmod_self`.

Both extension statements make `Hom(-, W)` exact on the groups killed by `n`
(`Function.Exact.compHom'` and `Function.Exact.compHom'_of_baer`, through the common
`Function.Exact.compHom'_of_forall_exists_comp_eq`). These are the algebraic inputs to the duality
statements for the finite `𝔽_p[G]`-modules and the finite `ℤ/pⁱ[G]`-modules of a profinite group.

## Main results

* `AddMonoidHom.exists_comp_eq_of_injective`: for `p` prime and `B` killed by `p`, every additive
  homomorphism `A →+ N` is the restriction along an injective `f : A →+ B` of an additive
  homomorphism `B →+ N`.
* `AddMonoidHom.exists_comp_eq_of_injective_of_baer`: for `B` killed by `n` and `W` satisfying
  Baer's criterion over `ℤ/nℤ`, every additive homomorphism `A →+ W` is the restriction along an
  injective `f : A →+ B` of an additive homomorphism `B →+ W`.
* `Function.Exact.compHom'`: `Hom(-, W)` is exact on the groups killed by `p`: an exact pair
  `X → Y → Z` with `Z` killed by `p` dualises to an exact pair `Hom(Z, W) → Hom(Y, W) → Hom(X, W)`.
* `Function.Exact.compHom'_of_baer`: `Hom(-, W)` is exact on the groups killed by `n` when `W`
  satisfies Baer's criterion over `ℤ/nℤ`.

In the exactness statements, `X` only needs addition and an additive identity; `Y` and `Z`
are additive commutative groups.
-/

public section

variable {p : ℕ} [Fact p.Prime] {A B N : Type*} [AddCommGroup A] [AddCommGroup B] [AddZero N]

/-- **Extension along an injection into a group killed by a prime.** If `p` is prime and `B` is
killed by `p`, every additive homomorphism `φ : A →+ N` extends along an injective additive
homomorphism `f : A →+ B` to a homomorphism `ψ : B →+ N` with `ψ ∘ f = φ`. Only addition and
zero are needed on `N`, with no algebraic laws: the injection has an additive left inverse. -/
theorem AddMonoidHom.exists_comp_eq_of_injective (hB : ∀ b : B, p • b = 0)
    {f : A →+ B} (hf : Function.Injective f) (φ : A →+ N) :
    ∃ ψ : B →+ N, ψ.comp f = φ := by
  have hA : ∀ a : A, p • a = 0 := fun a => hf (by rw [map_nsmul, hB, map_zero])
  let := AddCommGroup.zmodModule hA
  let := AddCommGroup.zmodModule hB
  obtain ⟨g, hg⟩ := (f.toZModLinearMap p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  refine ⟨φ.comp g.toAddMonoidHom, AddMonoidHom.ext fun a => ?_⟩
  simpa using congrArg φ (LinearMap.congr_fun hg a)

/-- **Extension along an injection into a group killed by `n`, into a Baer target.** If `B` is
killed by `n` and `W` satisfies Baer's criterion over `ℤ/nℤ`, then every additive homomorphism
`φ : A →+ W` extends along an injective additive homomorphism `f : A →+ B` to a homomorphism
`ψ : B →+ W` with `ψ ∘ f = φ`. The groups `A` and `B` are `ℤ/nℤ`-modules, every additive
homomorphism between `ℤ/nℤ`-modules is linear, and `Module.Baer.extension_property` extends the
linear map `φ` along `f`. At `n = 0` this is the extension property of a divisible group. -/
theorem AddMonoidHom.exists_comp_eq_of_injective_of_baer {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module (ZMod n) W] (hW : Module.Baer (ZMod n) W)
    (hB : ∀ b : B, n • b = 0) {f : A →+ B} (hf : Function.Injective f) (φ : A →+ W) :
    ∃ ψ : B →+ W, ψ.comp f = φ := by
  have hA : ∀ a : A, n • a = 0 := fun a => hf (by rw [map_nsmul, hB, map_zero])
  let := AddCommGroup.zmodModule hA
  let := AddCommGroup.zmodModule hB
  obtain ⟨ψ, hψ⟩ := hW.extension_property (f.toZModLinearMap n) hf (φ.toZModLinearMap n)
  exact ⟨ψ.toAddMonoidHom, AddMonoidHom.ext fun a => LinearMap.congr_fun hψ a⟩

/-- **`Hom(-, W)` is exact on groups killed by a prime.** If `X → Y → Z` is an exact pair of
additive homomorphisms, with `Y` and `Z` additive commutative groups and `Z` killed by `p`, then
for every additive commutative monoid `W` the pair
`Hom(Z, W) → Hom(Y, W) → Hom(X, W)` obtained by precomposition is exact.
The source `X` only needs addition and an additive identity. -/
theorem Function.Exact.compHom' {X Y Z W : Type*} [AddZeroClass X] [AddCommGroup Y]
    [AddCommGroup Z] [AddCommMonoid W] {f : X →+ Y} {g : Y →+ Z} (h : Function.Exact f g)
    (hZ : ∀ z : Z, p • z = 0) :
    Function.Exact (g.compHom' (P := W)) (f.compHom') :=
  h.compHom'_of_forall_exists_comp_eq fun φ =>
    AddMonoidHom.exists_comp_eq_of_injective hZ (QuotientAddGroup.kerLift_injective g) φ

/-- **`Hom(-, W)` is exact on groups killed by `n`, for a Baer target.** If `X → Y → Z` is an
exact pair of additive homomorphisms, with `Y` and `Z` additive commutative groups and `Z` killed
by `n`, and `W` satisfies Baer's criterion over `ℤ/nℤ`, then the pair
`Hom(Z, W) → Hom(Y, W) → Hom(X, W)` obtained by precomposition is exact.
The source `X` only needs addition and an additive identity. -/
theorem Function.Exact.compHom'_of_baer {n : ℕ} {X Y Z W : Type*} [AddZeroClass X]
    [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W] [Module (ZMod n) W]
    (hW : Module.Baer (ZMod n) W) {f : X →+ Y} {g : Y →+ Z} (h : Function.Exact f g)
    (hZ : ∀ z : Z, n • z = 0) :
    Function.Exact (g.compHom' (P := W)) (f.compHom') :=
  h.compHom'_of_forall_exists_comp_eq fun φ =>
    AddMonoidHom.exists_comp_eq_of_injective_of_baer hW hZ (QuotientAddGroup.kerLift_injective g) φ
