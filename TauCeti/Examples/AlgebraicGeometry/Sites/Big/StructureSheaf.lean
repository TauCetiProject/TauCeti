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

/-!
# Examples: values of `𝔾_a`, `𝔾_m` and `μ_n` on the big site

The structure sheaf of the big fpqc site over a scheme `S` and the sheaves `𝔾_a`, `𝔾_m` and
`μ_n` (`AlgebraicGeometry.Scheme.bigStructureSheaf`, `Ga`, `Gm`, `mu`) are evaluated on affine test
schemes `Spec R ⟶ S`, where they are `R`, `R`, `Rˣ` and the `n`-th roots of unity of `R`:

* the big structure sheaf vanishes on the empty test scheme;
* `𝔾_m(Spec ℚ) = ℚˣ` and `μ_2(Spec ℚ) = {±1}`, which has two elements;
* over `𝔽_p`, `μ_p` has only the trivial section on every reduced test scheme, but the section
  `1 + ε` on `Spec 𝔽_p[ε]/(ε^p)` is nontrivial, so `μ_p` is not the zero sheaf.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite

namespace TauCeti.AlgebraicGeometry.BigSiteExamples

universe u

variable {S : Scheme.{u}}

/-- **The big structure sheaf vanishes on the empty test scheme**: its value is the zero ring. -/
theorem subsingleton_bigStructureSheaf_obj_of_isEmpty (T : Over S) [IsEmpty T.left] :
    Subsingleton ((Scheme.bigStructureSheaf S).obj.obj (op T)) :=
  inferInstanceAs (Subsingleton Γ(T.left, ⊤))

/-- The value of `𝔾_a` on an affine test scheme `Spec R ⟶ S` is `R`. -/
noncomputable def gaObjSpecEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Scheme.Ga S).obj.obj (op (Over.mk h)) ≃+ R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toAddEquiv

/-- The value of `𝔾_m` on an affine test scheme `Spec R ⟶ S` is the unit group of `R`, written
additively. -/
noncomputable def gmObjSpecEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Scheme.Gm S).obj.obj (op (Over.mk h)) ≃+ Additive Rˣ :=
  let e : Additive Γ(Spec R, ⊤)ˣ ≃+ Additive Rˣ := MulEquiv.toAdditive
    (Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv)
  e

/-- The value of `μ_n` on an affine test scheme `Spec R ⟶ S` is the group of `n`-th roots of unity
of `R`, written additively. -/
noncomputable def muObjSpecEquiv (n : ℕ) (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Scheme.mu S n).obj.obj (op (Over.mk h)) ≃+ Additive (rootsOfUnity n R) :=
  let e : Additive (rootsOfUnity n Γ(Spec R, ⊤)) ≃+ Additive (rootsOfUnity n R) :=
    MulEquiv.toAdditive
      ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.restrictRootsOfUnity n)
  e

/-- The rational numbers as an object of `CommRingCat`. -/
abbrev ratRing : CommRingCat := .of ℚ

/-- **`𝔾_m(Spec ℚ) = ℚˣ`**: the value of `𝔾_m` over `Spec ℚ` on `Spec ℚ` itself. -/
noncomputable def gmObjSpecRatEquiv :
    (Scheme.Gm (Spec ratRing)).obj.obj (op (Over.mk (𝟙 (Spec ratRing)))) ≃+ Additive ℚˣ :=
  gmObjSpecEquiv ratRing (𝟙 _)

/-- **`μ_2(Spec ℚ) = {±1}`**: the value of `μ_2` over `Spec ℚ` on `Spec ℚ` itself has two
elements. -/
theorem card_muObjSpecRat :
    Nat.card ((Scheme.mu (Spec ratRing) 2).obj.obj (op (Over.mk (𝟙 (Spec ratRing))))) =
      2 := by
  rw [Nat.card_congr (muObjSpecEquiv 2 ratRing (𝟙 _)).toEquiv]
  change Nat.card (rootsOfUnity 2 ℚ) = 2
  exact (IsPrimitiveRoot.neg_one (R := ℚ) 0 (by norm_num)).card_rootsOfUnity

/-- Over a reduced ring of characteristic `p`, the only `p`-th root of unity is `1`: if `x^p = 1`
then `(x - 1)^p = x^p - 1 = 0`. -/
theorem rootsOfUnity_prime_eq_one_of_isReduced (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R]
    [CharP R p] [IsReduced R] (ζ : rootsOfUnity p R) : ζ = 1 := by
  have hζ : ((ζ : Rˣ) : R) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p (ζ : Rˣ)).1 ζ.prop, Units.val_one]
  have h : (((ζ : Rˣ) : R) - 1) ^ p = 0 := by rw [sub_pow_char, hζ, one_pow, sub_self]
  ext
  exact sub_eq_zero.1 (IsNilpotent.eq_zero ⟨p, h⟩)

/-- **`μ_p` vanishes on reduced test schemes in characteristic `p`.** For an affine test scheme
`Spec R ⟶ S` with `R` reduced of characteristic `p`, `μ_p(Spec R)` is trivial. -/
theorem subsingleton_muObjSpec_of_isReduced (p : ℕ) [Fact p.Prime] (R : CommRingCat.{u})
    [CharP R p] [IsReduced R] (h : Spec R ⟶ S) :
    Subsingleton ((Scheme.mu S p).obj.obj (op (Over.mk h))) :=
  (muObjSpecEquiv p R h).toEquiv.subsingleton_congr.2
    ⟨fun ζ η ↦ Additive.toMul.injective <|
      (rootsOfUnity_prime_eq_one_of_isReduced p R ζ.toMul).trans
        (rootsOfUnity_prime_eq_one_of_isReduced p R η.toMul).symm⟩

/-- **`μ_p` is nonzero on a nonreduced test scheme in characteristic `p`.** If `R` has
characteristic `p` and a nonzero element `ε` with `ε^p = 0`, then `1 + ε` is a `p`-th root of unity
different from `1`, so `μ_p(Spec R)` is nontrivial. -/
theorem nontrivial_muObjSpec_of_pow_eq_zero (p : ℕ) [Fact p.Prime] (R : CommRingCat.{u})
    [CharP R p] {ε : R} (hε : ε ^ p = 0) (hε0 : ε ≠ 0) (h : Spec R ⟶ S) :
    Nontrivial ((Scheme.mu S p).obj.obj (op (Over.mk h))) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hx : (1 + ε) ^ p = 1 := by rw [add_pow_char, one_pow, hε, add_zero]
  refine (muObjSpecEquiv p R h).toEquiv.nontrivial_congr.2 ⟨⟨Additive.ofMul
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
over `𝔽_p`, although it vanishes on reduced test schemes. -/
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
