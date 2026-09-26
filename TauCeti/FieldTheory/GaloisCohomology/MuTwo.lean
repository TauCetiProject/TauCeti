/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2
public import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# The `μ₂` coefficients as trivial `F₂` coefficients

Let `K` be a field with `[Invertible (2 : K)]` and `G_K = AbsoluteGaloisGroup K`. This file
identifies the Kummer coefficient module `μ₂ = μ₂(Kˢ)` of `TauCeti.Kummer` with the trivial `𝔽₂`
coefficient object `TauCeti.trivialF2 G_K` of the profinite-cohomology layer.

The identification is elementary: an element of `μ₂` is a root of unity `ζ` of a separable closure
with `ζ ^ 2 = 1`, so `ζ` is `±1`, and `±1 ∈ K`, so the Galois action on `μ₂` is trivial
(`TauCeti.mu2_smul_eq_self`). The value dictionary `TauCeti.mu2EquivZMod2` is the specialization of
the general roots-of-unity dictionary `IsPrimitiveRoot.zmodEquivRootsOfUnity` of
`TauCeti.RingTheory.RootsOfUnity.ZMod` at the primitive root `-1`, which is primitive at every
characteristic other than `2` (`IsPrimitiveRoot.neg_one`); it sends `0` to `0` and `-1` to `1`,
and its type pins it, because `ZMod 2` has no additive self-equivalence other than the identity,
so sending `0` to `0` already determines it.

Crossed with the universe lift of `TauCeti.trivialF2Equiv` and read in the category
`TopRep ℤ G_K`, this is the isomorphism of coefficient objects
`TauCeti.kummerCoeffIsoTrivialF2`, the only coefficient transport used at `n = 2`. Nothing here is
specific to local fields: the action on `μ₂` is trivial over every field, and the hypothesis
`[Invertible (2 : K)]` is what makes `1` and `-1` distinct, so that `μ₂` has two elements and the
dictionary with `ZMod 2` exists at all. Over a field of characteristic `2` the second roots of
unity are the single element `1 = -1`, which `ZMod 2` is not.

## Main definitions

* `TauCeti.mu2NegOne`: the nontrivial element of `μ₂`, that is `-1` read as a `2`nd root of unity.
* `TauCeti.mu2EquivZMod2`: the value dictionary `μ₂ ≃+ ZMod 2`.
* `TauCeti.kummerCoeffEquiv`: the same dictionary, crossed with the universe lift, as an additive
  equivalence of the coefficient carriers `KummerCoeff K 2 ≃+ (trivialF2 G_K).V`.
* `TauCeti.kummerCoeffIsoTrivialF2`: the isomorphism of coefficient objects
  `ofDiscreteModule ℤ G_K (KummerCoeff K 2) ≅ trivialF2 G_K`.
* `TauCeti.kummerClass`: the Kummer class `(a) ∈ H¹(G_K, 𝔽₂)` of a unit, read in the
  `trivialF2 G_K` carrier.

## Main results

* `TauCeti.toMul_eq_one_or_neg_one` and `TauCeti.eq_zero_or_eq_mu2NegOne`: the `2`nd roots of
  unity of a separable closure are `1` and `-1`, so an element of `μ₂` is `0` or `mu2NegOne`.
* `TauCeti.mu2NegOne_ne_zero` and `TauCeti.zero_ne_mu2NegOne`: the two elements of `μ₂` are
  distinct, because `2` is invertible in `K`.
* `TauCeti.mu2EquivZMod2_apply_zero`, `TauCeti.mu2EquivZMod2_apply_mu2NegOne`,
  `TauCeti.mu2EquivZMod2_eq_one_iff`: the value dictionary on its two values.
* `TauCeti.mu2_smul_eq_self`: the Galois action on `μ₂` is trivial.
* `TauCeti.mu2EquivZMod2_equivariant`: the value dictionary is fixed by `G_K`, which is what makes
  it a morphism of coefficient objects.
* `TauCeti.kummerClass_eq_zero_of_square`: the Kummer class of a square vanishes.
-/

public section

open scoped ContRepresentation

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable {K : Type u} [Field K]

/-! ### The elements of `μ₂` -/

/-- The nontrivial element of `μ₂`, that is `-1` read as a `2`nd root of unity in a separable
closure of the base field. -/
noncomputable def mu2NegOne : KummerCoeff K 2 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (-1 : (SeparableClosure K)) (by simp))

/-- The underlying unit of `TauCeti.mu2NegOne` is `-1`, so `mu2NegOne` is the second root of
unity of a separable closure that is not the first. -/
@[simp]
theorem toMul_mu2NegOne : mu2NegOne.toMul.1 = (-1 : (SeparableClosure K)ˣ) :=
  Units.ext (by simp [mu2NegOne])

/-- **The `2`nd roots of unity of a separable closure are `1` and `-1`**: `ζ ^ 2 = 1` in a field
forces `ζ = 1` or `ζ = -1`. No hypothesis on the characteristic is needed here: in characteristic
two the two values coincide (`-1 = 1`), which is why the two roots are shown to be *distinct* only
under `[Invertible (2 : K)]` (`TauCeti.mu2NegOne_ne_zero`). -/
theorem toMul_eq_one_or_neg_one (x : KummerCoeff K 2) :
    x.toMul = 1 ∨ x.toMul.1 = -1 := by
  have hu : (x.toMul.1 : (SeparableClosure K)ˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 _).1 x.toMul.2
  rcases sq_eq_one_iff.mp (congrArg Units.val hu) with h | h
  · exact Or.inl (Subtype.ext (Units.ext h))
  · exact Or.inr (Units.ext h)

/-- An element of `μ₂` is `0` or `-1`. -/
theorem eq_zero_or_eq_mu2NegOne (x : KummerCoeff K 2) :
    x = 0 ∨ x = mu2NegOne := by
  rcases toMul_eq_one_or_neg_one x with h | h
  · exact Or.inl (Additive.toMul.injective h)
  · exact Or.inr (Additive.toMul.injective (Subtype.ext (h.trans toMul_mu2NegOne.symm)))

/-- The separable closure of a field in which `2` is invertible does not have characteristic `2`:
`2` would then vanish in it, and it does not, because the algebra map into it is injective. -/
private theorem ringChar_ne_two [Invertible (2 : K)] : ringChar (SeparableClosure K) ≠ 2 := by
  intro h
  have hz : (2 : (SeparableClosure K)) = 0 :=
    (ringChar.spec (SeparableClosure K) 2).mpr (h ▸ dvd_rfl)
  exact (map_ne_zero (algebraMap K (SeparableClosure K)) (a := (2 : K))).mpr
    (Invertible.ne_zero (2 : K)) hz

/-- `-1` is not `1` in a separable closure of a field in which `2` is invertible: its
characteristic is not `2`, and characteristic `≠ 2` is what separates `-1` from `1`. -/
private theorem neg_one_ne_one [Invertible (2 : K)] : (-1 : (SeparableClosure K)) ≠ 1 :=
  Ring.neg_one_ne_one_of_char_ne_two ringChar_ne_two

/-- The two elements of `μ₂` are distinct, because `2` is invertible in the base field. -/
theorem mu2NegOne_ne_zero [Invertible (2 : K)] : mu2NegOne ≠ (0 : KummerCoeff K 2) := by
  intro h
  have h1 : (-1 : (SeparableClosure K)ˣ) = 1 := by
    simpa using congrArg Subtype.val (congrArg Additive.toMul h)
  exact neg_one_ne_one <| by simpa using congrArg Units.val h1

/-- The two elements of `μ₂` are distinct, read in the other order. -/
theorem zero_ne_mu2NegOne [Invertible (2 : K)] : (0 : KummerCoeff K 2) ≠ mu2NegOne :=
  mu2NegOne_ne_zero.symm

/-! ### The trivial Galois action -/

variable (K)

/-- **The Galois action on `μ₂` is trivial.** Every `2`nd root of unity in a separable closure is
`±1` (TauCeti.toMul_eq_one_or_neg_one), hence lies in the base field and is fixed by `G_K`. This
is what makes the Kummer coefficients at `n = 2` isomorphic to the trivial `F₂` coefficient
object, whereas the action on `μₙ` for `n > 2` is not trivial in general. It is a statement about
a field in any characteristic: the hypothesis `[Invertible (2 : K)]` is what tells the two roots
apart, not what triviality of the action needs. -/
theorem mu2_smul_eq_self (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    g • x = x := by
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  rcases toMul_eq_one_or_neg_one x with h | h <;> simp [h]

/-! ### The value dictionary -/

variable [Invertible (2 : K)]

/-- **`-1` is a primitive `2`nd root of unity in a separable closure**: this is Mathlib's
`IsPrimitiveRoot.neg_one`, read at the characteristic of the separable closure, which is not `2`
because `2` is invertible in the base field, and transferred to the units by
`IsPrimitiveRoot.coe_units_iff`. It is what makes the value dictionary the specialization of the
general roots-of-unity equivalence `IsPrimitiveRoot.zmodEquivRootsOfUnity` of
`TauCeti.RingTheory.RootsOfUnity.ZMod` rather than a hand-built one. -/
private theorem isPrimitiveRoot_mu2NegOne : IsPrimitiveRoot (-1 : (SeparableClosure K)ˣ) 2 := by
  have h : IsPrimitiveRoot (-1 : (SeparableClosure K)) 2 :=
    IsPrimitiveRoot.neg_one (p := ringChar (SeparableClosure K)) (h := ringChar.of_eq rfl)
      ringChar_ne_two
  exact IsPrimitiveRoot.coe_units_iff.mp h

/-- **The `μ₂` coefficient module is `ZMod 2`**, as an additive group: it is the specialization of
`IsPrimitiveRoot.zmodEquivRootsOfUnity` at the primitive root `-1` (`IsPrimitiveRoot.neg_one`,
since the characteristic of `Kˢ` is not `2` when `2` is invertible in `K`), read backwards. The
generator is canonical: it is the nontrivial element `-1` of `μ₂`, so the dictionary sends `0` to
`0` and `-1` to `1`, and there is only one additive equivalence `ZMod 2 ≃+ ZMod 2`. -/
noncomputable def mu2EquivZMod2 : KummerCoeff K 2 ≃+ ZMod 2 :=
  (isPrimitiveRoot_mu2NegOne K).zmodEquivRootsOfUnity.symm

/-- The value dictionary sends the zero element of `μ₂` to `0`. -/
@[simp]
theorem mu2EquivZMod2_apply_zero : mu2EquivZMod2 K 0 = 0 := by
  have h0 : (isPrimitiveRoot_mu2NegOne K).zmodEquivRootsOfUnity 0 = 0 :=
    (isPrimitiveRoot_mu2NegOne K).zmodEquivRootsOfUnity.map_zero
  rw [mu2EquivZMod2, ← h0, AddEquiv.symm_apply_apply]

/-- The value dictionary sends the nontrivial element of `μ₂` to `1`, read at the exponent
`1` from the inverse rule `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_pow`. -/
@[simp]
theorem mu2EquivZMod2_apply_mu2NegOne : mu2EquivZMod2 K mu2NegOne = 1 := by
  -- `mu2NegOne` is `-1` read as a `2`nd root of unity, so it is the element `ζ ^ 1` that the
  -- inverse rule is specialized at, for `ζ = -1` and `i = 1`.
  have hone : Additive.ofMul ⟨(-1 : (SeparableClosure K)ˣ) ^ (1 : ℕ), by simp⟩ = mu2NegOne := by
    refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
    simp [toMul_mu2NegOne]
  have hone' :=
    (isPrimitiveRoot_mu2NegOne K).zmodEquivRootsOfUnity_symm_apply_pow (1 : ℕ) (by simp)
  rw [mu2EquivZMod2, ← hone, hone', Nat.cast_one]

/-- The value dictionary sends an element of `μ₂` to `1` exactly when it is the nontrivial
element: the dictionary is an equivalence, and it sends `mu2NegOne` to `1`. -/
@[simp]
theorem mu2EquivZMod2_eq_one_iff (x : KummerCoeff K 2) :
    mu2EquivZMod2 K x = 1 ↔ x = mu2NegOne := by
  rw [← mu2EquivZMod2_apply_mu2NegOne (K := K), AddEquiv.apply_eq_iff_eq]

/-- The `μ₂` coefficient identification is equivariant: the Galois action on `μ₂` is trivial, so
the value dictionary is fixed by `G_K`. This is what makes the Kummer coefficients at `n = 2`
isomorphic to a trivial coefficient object. -/
theorem mu2EquivZMod2_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    mu2EquivZMod2 K (g • x) = mu2EquivZMod2 K x :=
  congrArg (mu2EquivZMod2 K) (mu2_smul_eq_self K g x)

/-! ### The coefficient object -/

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The coefficient carriers of `μ₂` and of the trivial `𝔽₂` object are the same additive
group.** This is `TauCeti.mu2EquivZMod2` crossed with the universe lift of
`TauCeti.trivialF2Equiv`; it is the dictionary read on carriers, and
`TauCeti.kummerCoeffIsoTrivialF2` is the same dictionary read in the category `TopRep ℤ G_K`. -/
noncomputable def kummerCoeffEquiv :
    KummerCoeff K 2 ≃+ (trivialF2 (AbsoluteGaloisGroup K)).V :=
  (mu2EquivZMod2 K).trans (trivialF2Equiv (AbsoluteGaloisGroup K)).symm

/-- The dictionary is the value dictionary crossed with the universe lift. -/
@[simp]
theorem kummerCoeffEquiv_apply (x : KummerCoeff K 2) :
    kummerCoeffEquiv K x = (trivialF2Equiv (AbsoluteGaloisGroup K)).symm (mu2EquivZMod2 K x) := by
  rw [kummerCoeffEquiv, AddEquiv.trans_apply]

/-- The inverse dictionary reads a value through the universe lift. -/
@[simp]
theorem kummerCoeffEquiv_symm_apply (b : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    (kummerCoeffEquiv K).symm b =
      (mu2EquivZMod2 K).symm (trivialF2Equiv (AbsoluteGaloisGroup K) b) := by
  rw [kummerCoeffEquiv, AddEquiv.symm_trans_apply]
  have hsymm : (trivialF2Equiv (AbsoluteGaloisGroup K)).symm.symm b
      = trivialF2Equiv (AbsoluteGaloisGroup K) b :=
    Equiv.symm_symm_apply (trivialF2Equiv (AbsoluteGaloisGroup K)).toEquiv b
  rw [hsymm]

/-- The dictionary is `G_K`-equivariant, the two sides being the trivial action. -/
private theorem kummerCoeffEquiv_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    kummerCoeffEquiv K (g • x) = g • kummerCoeffEquiv K x := by
  simp only [kummerCoeffEquiv_apply, mu2EquivZMod2_equivariant,
    TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]

private noncomputable def kummerCoeffToTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V :=
  ofDiscreteModuleMap (kummerCoeffEquiv K).toIntLinearEquiv (kummerCoeffEquiv_equivariant K)

private noncomputable def kummerCoeffFromTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) :=
  ofDiscreteModuleMap (kummerCoeffEquiv K).symm.toIntLinearEquiv
    (fun g b => AddEquiv.symm_map_smul_of_map_smul (kummerCoeffEquiv K)
      (kummerCoeffEquiv_equivariant K) g b)

private theorem kummerCoeffToTrivialF2_apply (x : KummerCoeff K 2) :
    (kummerCoeffToTrivialF2 K) x = kummerCoeffEquiv K x :=
  ofDiscreteModuleMap_hom_apply _ _ _

private theorem kummerCoeffFromTrivialF2_apply (b : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    (kummerCoeffFromTrivialF2 K) b = (kummerCoeffEquiv K).symm b :=
  ofDiscreteModuleMap_hom_apply _ _ _

/-- **The Kummer coefficients at `n = 2` and the trivial `𝔽₂` coefficient object are the same
coefficient object.** The isomorphism is the value dictionary of `TauCeti.mu2EquivZMod2`, crossed
with the universe lift of `TauCeti.trivialF2Equiv`, and it is a morphism of coefficient objects
because the Galois action on `μ₂` is trivial (`TauCeti.mu2_smul_eq_self`). This is the
only coefficient transport used at `n = 2`. -/
noncomputable def kummerCoeffIsoTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) ≅
      trivialF2 (AbsoluteGaloisGroup K) := by
  rw [← ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)]
  exact
    { hom := kummerCoeffToTrivialF2 K
      inv := kummerCoeffFromTrivialF2 K
      -- Both round trips rewrap the *same* additive equivalence, so each is an identity of
      -- additive equivalences. The goal of an inverse law is stated through the `hom`/`inv` fields
      -- of the isomorphism, as a `TopRep.Hom` composite, and no stable rewrite reaches the
      -- carrier-level goal: `TopRep.comp_apply` is stated on carriers, and the carrier of
      -- `TauCeti.ofDiscreteModule` is not syntactically the module. `change` is what exposes the
      -- composite, after which the two application rules above and the inverse rule of `AddEquiv`
      -- finish the goal.
      hom_inv_id := by
        refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : KummerCoeff K 2) => ?_)
        change (kummerCoeffFromTrivialF2 K) ((kummerCoeffToTrivialF2 K) m) = m
        rw [kummerCoeffToTrivialF2_apply, kummerCoeffFromTrivialF2_apply,
          AddEquiv.symm_apply_apply]
      inv_hom_id := by
        refine TopRep.hom_ext
          (DFunLike.ext _ _ fun (b : (trivialF2 (AbsoluteGaloisGroup K)).V) => ?_)
        change (kummerCoeffToTrivialF2 K) ((kummerCoeffFromTrivialF2 K) b) = b
        rw [kummerCoeffFromTrivialF2_apply, kummerCoeffToTrivialF2_apply,
          AddEquiv.apply_symm_apply] }

/-! ### The Kummer class of a unit -/

variable {K}

/-- **The Kummer class** `(a) ∈ H¹(G_K, 𝔽₂)` of a unit `a`: the canonical Kummer map
`TauCeti.kummerMapCanonical` at `n = 2`, read through the coefficient-object isomorphism
`TauCeti.kummerCoeffIsoTrivialF2`. -/
noncomputable def kummerClass (a : Kˣ) :
    continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (ContinuousCohomology.coeffMap (kummerCoeffIsoTrivialF2 K).hom 1).hom
    (Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_of_invertible (2 : K)) a))

variable (K)

/-- **The Kummer class of a square vanishes.** A member of `Subgroup.square Kˣ` is a square, hence
a two-th power, so `TauCeti.kummerMap_eq_one_iff` at `n = 2` makes the Kummer map trivial on it, and
the degree-one comparison `TauCeti.explicitIso_kummerMap` carries that to the Kummer class. -/
theorem kummerClass_eq_zero_of_square {a : Kˣ} (ha : a ∈ Subgroup.square Kˣ) :
    kummerClass a = 0 := by
  obtain ⟨r, hr⟩ := Subgroup.mem_square.mp ha
  have hone : kummerMap K 2 (isUnit_of_invertible (2 : K)) a = 1 :=
    (kummerMap_eq_one_iff (isUnit_of_invertible (2 : K)) a).mpr
      ⟨r, by rw [hr, pow_two]⟩
  have hzero : Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_of_invertible (2 : K)) a)
      = 0 := by
    rw [explicitIso_kummerMap K 2 (isUnit_of_invertible (2 : K)) a, hone]
    simp
  rw [kummerClass, hzero]
  simp


end TauCeti
