/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Examples: values of `𝔾_a`, `𝔾_m` and `μ_n` on the big site

Checks on the structure sheaf of the big fpqc site over a scheme `S` and the sheaves `𝔾_a`,
`𝔾_m` and `μ_n` (`AlgebraicGeometry.Scheme.bigStructureSheaf`, `Ga`, `Gm`, `mu`), whose values on
affine test schemes `Spec R ⟶ S` are `R`, `R`, `Rˣ` and the `n`-th roots of unity of `R`
(`Scheme.gaObjSpecEquiv`, `Scheme.gmObjSpecEquiv`, `Scheme.muObjSpecEquiv`):

* the big structure sheaf vanishes on the empty test scheme;
* `𝔾_m(Spec ℚ) = ℚˣ`, and `μ_2(Spec ℚ)` has two elements;
* in characteristic `p`, `μ_{pʲ}` has only the trivial section on every reduced test scheme, but
  the section `1 + ε` of `μ_p` on `Spec 𝔽_p[ε]/(ε^p)` is nontrivial, so `μ_p` is not the zero
  sheaf over `𝔽_p`.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Polynomial

namespace TauCeti.AlgebraicGeometry.BigSiteExamples

universe u

variable {S : Scheme.{u}}

/-- **The big structure sheaf vanishes on the empty test scheme**: its value is the zero ring. -/
theorem subsingleton_bigStructureSheaf_obj_of_isEmpty (T : Over S) [IsEmpty T.left] :
    Subsingleton ((Scheme.bigStructureSheaf S).obj.obj (op T)) := by
  rw [Scheme.bigStructureSheaf_obj]
  infer_instance

/-- The rational numbers as an object of `CommRingCat`. -/
abbrev ratRing : CommRingCat := .of ℚ

/-- **`𝔾_m(Spec ℚ) = ℚˣ`**: the value of `𝔾_m` over `Spec ℚ` on `Spec ℚ` itself. -/
noncomputable def gmObjSpecRatEquiv :
    (Scheme.Gm (Spec ratRing)).obj.obj (op (Over.mk (𝟙 (Spec ratRing)))) ≃+ Additive ℚˣ :=
  Scheme.gmObjSpecEquiv _ ratRing (𝟙 _)

/-- **`μ_2(Spec ℚ)` has two elements**: the value of `μ_2` over `Spec ℚ` on `Spec ℚ` itself is
`rootsOfUnity 2 ℚ = {±1}`. -/
theorem card_muObjSpecRat :
    Nat.card ((Scheme.mu (Spec ratRing) 2).obj.obj (op (Over.mk (𝟙 (Spec ratRing))))) =
      2 := by
  rw [Nat.card_congr ((Scheme.muObjSpecEquiv _ 2 ratRing (𝟙 _)).toEquiv.trans Additive.toMul)]
  exact (IsPrimitiveRoot.neg_one (R := ℚ) 0 (by norm_num)).card_rootsOfUnity

/-- **`μ_{pʲ}` vanishes on reduced test schemes in characteristic `p`.** For every `S`-scheme `T`
that is reduced and whose global sections have exponential characteristic `p`, `μ_{pʲ}(T)` is
trivial: a `pʲ`-th root of unity `u` satisfies `(u - 1) ^ pʲ = 0`. -/
theorem subsingleton_mu_obj_of_isReduced (p j : ℕ) (T : Over S) [IsReduced T.left]
    [ExpChar Γ(T.left, ⊤) p] : Subsingleton ((Scheme.mu S (p ^ j)).obj.obj (op T)) := by
  rw [Scheme.mu_obj]
  have := subsingleton_rootsOfUnity_prime_pow (R := Γ(T.left, ⊤)) p j
  infer_instance

/-- **`μ_p` is nonzero on a nonreduced test scheme in characteristic `p`.** If `R` has
characteristic `p` and a nonzero element `ε` with `ε^p = 0`, then `1 + ε` is a `p`-th root of unity
different from `1`, so `μ_p(Spec R)` is nontrivial. -/
theorem nontrivial_muObjSpec_of_pow_eq_zero (p : ℕ) [Fact p.Prime] (R : CommRingCat.{u})
    [CharP R p] {ε : R} (hε : ε ^ p = 0) (hε0 : ε ≠ 0) (h : Spec R ⟶ S) :
    Nontrivial ((Scheme.mu S p).obj.obj (op (Over.mk h))) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hx : (1 + ε) ^ p = 1 := by rw [add_pow_char, one_pow, hε, add_zero]
  refine (Scheme.muObjSpecEquiv S p R h).toEquiv.nontrivial_congr.2 ⟨⟨Additive.ofMul
    (rootsOfUnity.mkOfPowEq (1 + ε) hx), 0, fun he ↦ hε0 ?_⟩⟩
  have := congrArg (fun ζ : Additive (rootsOfUnity p R) ↦ ((ζ.toMul : Rˣ) : R)) he
  simpa using this

/-- **`μ_p` is not zero over `𝔽_p`.** The value of `μ_p` on `Spec 𝔽_p[ε]/(ε^p)`, over any base, is
nontrivial: `1 + ε` is a `p`-th root of unity different from `1`. So `μ_p` is not the zero sheaf
over `𝔽_p`, although it vanishes on reduced test schemes
(`subsingleton_mu_obj_of_isReduced`). Here `𝔽_p[ε]/(ε^p)` is the truncated polynomial algebra
`AdjoinRoot (X ^ p)`, with `ε` its root. -/
theorem nontrivial_muObjSpec_truncated (p : ℕ) [Fact p.Prime] {S : Scheme.{0}}
    (h : Spec (.of (AdjoinRoot ((X : (ZMod p)[X]) ^ p))) ⟶ S) :
    Nontrivial ((Scheme.mu S p).obj.obj (op (Over.mk h))) := by
  have hp := (Fact.out : p.Prime).one_lt
  have hε : AdjoinRoot.root ((X : (ZMod p)[X]) ^ p) ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow p) X_ne_zero (by simpa using hp)
  have : Nontrivial (AdjoinRoot ((X : (ZMod p)[X]) ^ p)) := ⟨⟨_, 0, hε⟩⟩
  have : CharP (AdjoinRoot ((X : (ZMod p)[X]) ^ p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  have hεp : AdjoinRoot.root ((X : (ZMod p)[X]) ^ p) ^ p = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  exact nontrivial_muObjSpec_of_pow_eq_zero p (.of (AdjoinRoot ((X : (ZMod p)[X]) ^ p))) hεp hε h

end TauCeti.AlgebraicGeometry.BigSiteExamples
