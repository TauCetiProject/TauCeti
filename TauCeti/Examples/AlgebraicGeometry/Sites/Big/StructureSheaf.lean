/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Div
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

open AlgebraicGeometry CategoryTheory Opposite

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

/-- The ideal `(X^p)` of `𝔽_p[X]`. -/
noncomputable abbrev truncatedIdeal (p : ℕ) : Ideal (Polynomial (ZMod p)) :=
  Ideal.span {Polynomial.X ^ p}

/-- The class `ε` of `X` in `𝔽_p[ε]/(ε^p)`. -/
noncomputable abbrev truncatedEps (p : ℕ) : Polynomial (ZMod p) ⧸ truncatedIdeal p :=
  Ideal.Quotient.mk _ Polynomial.X

lemma truncatedEps_pow (p : ℕ) : truncatedEps p ^ p = 0 :=
  (map_pow (Ideal.Quotient.mk _) _ _).symm.trans
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl))

lemma truncatedEps_ne_zero (p : ℕ) (hp : 1 < p) : truncatedEps p ≠ 0 := fun h ↦ by
  have h' := Ideal.Quotient.eq_zero_iff_mem.1 h
  rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at h'
  have : Fact (1 < p) := ⟨hp⟩
  exact one_ne_zero (Polynomial.coeff_X_one.symm.trans (h' 1 hp))

/-- **`μ_p` is not zero over `𝔽_p`.** The value of `μ_p` on `Spec 𝔽_p[ε]/(ε^p)`, over any base, is
nontrivial: `1 + ε` is a `p`-th root of unity different from `1`. So `μ_p` is not the zero sheaf
over `𝔽_p`, although it vanishes on reduced test schemes
(`subsingleton_mu_obj_of_isReduced`). -/
theorem nontrivial_muObjSpec_truncated (p : ℕ) [Fact p.Prime] {S : Scheme.{0}}
    (h : Spec (.of (Polynomial (ZMod p) ⧸ truncatedIdeal p)) ⟶ S) :
    Nontrivial ((Scheme.mu S p).obj.obj (op (Over.mk h))) := by
  have hp := (Fact.out : p.Prime).one_lt
  have : Nontrivial (Polynomial (ZMod p) ⧸ truncatedIdeal p) :=
    ⟨⟨_, 0, truncatedEps_ne_zero p hp⟩⟩
  have : CharP (Polynomial (ZMod p) ⧸ truncatedIdeal p) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  exact nontrivial_muObjSpec_of_pow_eq_zero p (.of _) (truncatedEps_pow p)
    (truncatedEps_ne_zero p hp) h

end TauCeti.AlgebraicGeometry.BigSiteExamples
