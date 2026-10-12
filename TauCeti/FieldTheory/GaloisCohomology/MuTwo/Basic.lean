/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
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

Crossed with the universe lift of `TauCeti.trivialF2Equiv`, the value dictionary is an
isomorphism of coefficient objects `TauCeti.kummerCoeffIsoTrivialF2` from the `KummerCoeff K 2`
object of `TopRep ℤ G_K` to the trivial `𝔽₂` object, which is the coefficient object that
degree-one continuous cohomology is written against here. Nothing here is specific to local
fields: the action on `μ₂` is trivial over every field, and the hypothesis
`[Invertible (2 : K)]` is what makes `1` and `-1` distinct, so that `μ₂` has two elements and the
dictionary with `ZMod 2` exists at all. Over a field of characteristic `2` the second roots of
unity are the single element `1 = -1`, which `ZMod 2` is not.

The Kummer class `(a) ∈ H¹(G_K, 𝔽₂)` of a unit `a` is read in that trivial carrier, and
`TauCeti.kummerSquareClassEquiv` identifies the square-class group `Kˣ ⧸ (Kˣ)²` with it by sending
the class of `a` to `(a)`.

## Main definitions

* `TauCeti.mu2NegOne`: the element of `μ₂` represented by `-1`, that is `-1` read as a `2`nd root
  of unity; it is the nontrivial element of `μ₂` when `[Invertible (2 : K)]` holds.
* `TauCeti.mu2EquivZMod2`: the value dictionary `μ₂ ≃+ ZMod 2`.
* `TauCeti.kummerCoeffEquiv`: the same dictionary, crossed with the universe lift, as an additive
  equivalence of the coefficient carriers `KummerCoeff K 2 ≃+ (trivialF2 G_K).V`.
* `TauCeti.kummerCoeffIsoTrivialF2`: the isomorphism of coefficient objects
  `ofDiscreteModule ℤ G_K (KummerCoeff K 2) ≅ trivialF2 G_K`, whose application rules
  `TauCeti.kummerCoeffIsoTrivialF2_hom_apply` and
  `TauCeti.kummerCoeffIsoTrivialF2_inv_apply` are the value dictionary and its inverse.
* `TauCeti.kummerClass`: the Kummer class `(a) ∈ H¹(G_K, 𝔽₂)` of a unit, read in the
  `trivialF2 G_K` carrier.
* `TauCeti.kummerCocycleModTwo` and `TauCeti.kummerCocycleModTwoClass`: the explicit
  `𝔽₂`-valued Kummer cocycle of a chosen square root and its cohomology class.
* `TauCeti.kummerSquareClassEquiv`: the Kummer isomorphism on the square-class group
  `Kˣ ⧸ (Kˣ)²`, an additive equivalence with `H¹(G_K, 𝔽₂)`.

## Main results

* `TauCeti.toMul_eq_one_or_neg_one` and `TauCeti.eq_zero_or_eq_mu2NegOne`: the `2`nd roots of
  unity of a separable closure are `1` and `-1`, so an element of `μ₂` is `0` or `mu2NegOne`.
* `TauCeti.mu2NegOne_ne_zero`: the two elements of `μ₂` are distinct, because `2` is invertible
  in `K`.
* `TauCeti.mu2EquivZMod2_apply_mu2NegOne`, `TauCeti.mu2EquivZMod2_eq_one_iff`: the value
  dictionary on the nontrivial element of `μ₂`.
* `TauCeti.mu2_smul_eq_self`: the Galois action on `μ₂` is trivial.
* `TauCeti.kummerClass_one` and `TauCeti.kummerClass_mul`: the Kummer class of a unit is a
  homomorphism from `Kˣ` into `H¹(G_K, 𝔽₂)` written additively.
* `TauCeti.mu2EquivZMod2_kummerCocycle` and `TauCeti.kummerCocycleModTwo_apply`: the Kummer
  cocycle, read in `ZMod 2`, is `0` when a Galois element fixes the chosen square root and `1`
  otherwise.
* `TauCeti.kummerCocycleModTwoClass_eq_explicitCoeff1Equiv`: the explicit mod-two cocycle class
  is the generic Kummer cocycle class read through the coefficient dictionary `μ₂ ≃ 𝔽₂`.
* `TauCeti.kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq`: that explicit class is the canonical
  Kummer class, under the degree-one comparison with continuous cohomology.
* `TauCeti.kummerClass_eq_zero_iff_square`: the Kummer class of a unit of `Kˣ` vanishes exactly
  at the squares in `Kˣ`.
* `TauCeti.kummerSquareClassEquiv_squareClass`: a square class is sent to the Kummer class of
  any of its representatives.
* `TauCeti.kummerClass_eq_kummerClass_iff_isSquare_mul`: two units have the same Kummer class
  exactly when their product is a square.
-/

public section

open scoped ContRepresentation

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable {K : Type u} [Field K]

/-! ### The elements of `μ₂` -/

/-- The element of `μ₂` represented by `-1`, that is `-1` read as a `2`nd root of unity in a
separable closure of the base field. It is the nontrivial element of `μ₂` when `2` is invertible in
`K` (`TauCeti.mu2NegOne_ne_zero`); in characteristic two `-1 = 1`, and then it is the element `0`
of `μ₂`. -/
noncomputable def mu2NegOne : KummerCoeff K 2 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (-1 : (SeparableClosure K)) (by simp))

/-- The underlying unit of `TauCeti.mu2NegOne` is `-1`, so `mu2NegOne` is exactly `-1` read
as a `2`nd root of unity in a separable closure of the base field. -/
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

/-! ### The trivial Galois action -/

variable (K)

/-- **The Galois action on `μ₂` is trivial.** Every `2`nd root of unity in a separable closure is
`±1` (TauCeti.toMul_eq_one_or_neg_one), hence lies in the base field and is fixed by `G_K`. This
is what makes the Kummer coefficients at `n = 2` isomorphic to the trivial `F₂` coefficient
object, whereas the action on `μₙ` for `n > 2` is not trivial in general. It is a statement about
a field in any characteristic: the hypothesis `[Invertible (2 : K)]` is what tells the two roots
apart, not what triviality of the action needs. -/
@[simp]
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
theorem kummerCoeffEquiv_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    kummerCoeffEquiv K (g • x) = g • kummerCoeffEquiv K x := by
  simp only [kummerCoeffEquiv_apply, mu2_smul_eq_self,
    TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]

/-- The coefficient dictionary read as a morphism of coefficient objects: the additive
equivalence `TauCeti.kummerCoeffEquiv` is `G_K`-equivariant, because the Galois action on `μ₂` is
trivial (`TauCeti.kummerCoeffEquiv_equivariant`) and the action on `TauCeti.trivialF2` is trivial
as well. -/
private noncomputable def kummerCoeffToTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V :=
  ofDiscreteModuleMap (kummerCoeffEquiv K).toIntLinearEquiv (kummerCoeffEquiv_equivariant K)

private theorem kummerCoeffToTrivialF2_apply (x : KummerCoeff K 2) :
    (kummerCoeffToTrivialF2 K) x = kummerCoeffEquiv K x :=
  ofDiscreteModuleMap_hom_apply _ _ _

/-- **The Kummer coefficients at `n = 2` and the trivial `𝔽₂` coefficient object are the same
coefficient object.** The isomorphism is the value dictionary of `TauCeti.mu2EquivZMod2`, crossed
with the universe lift of `TauCeti.trivialF2Equiv`, and it is a morphism of coefficient objects
because the Galois action on `μ₂` is trivial (`TauCeti.mu2_smul_eq_self`). The target is the
trivial `𝔽₂` object itself, `TauCeti.kummerClass` is that isomorphism read on degree-one continuous
cohomology, and its two application rules below are the value dictionary and its inverse. -/
noncomputable def kummerCoeffIsoTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) ≅
      trivialF2 (AbsoluteGaloisGroup K) :=
  (ofDiscreteModuleIso (kummerCoeffEquiv K).toIntLinearEquiv
    (kummerCoeffEquiv_equivariant K)).trans
    (eqToIso (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)))

/-- The coefficient isomorphism `TauCeti.kummerCoeffIsoTrivialF2` is the coefficient dictionary
`TauCeti.kummerCoeffToTrivialF2` followed by the transport of
`TauCeti.ofDiscreteModule_trivialF2`. -/
private theorem kummerCoeffIsoTrivialF2_hom :
    (kummerCoeffIsoTrivialF2 K).hom =
      kummerCoeffToTrivialF2 K ≫ eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)) :=
  congrArg (· ≫ eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)))
    (ofDiscreteModuleIso_hom (kummerCoeffEquiv K).toIntLinearEquiv
      (kummerCoeffEquiv_equivariant K))

/-- **The isomorphism reads on carriers as the value dictionary.** -/
@[simp]
theorem kummerCoeffIsoTrivialF2_hom_apply (x : KummerCoeff K 2) :
    (kummerCoeffIsoTrivialF2 K).hom x = kummerCoeffEquiv K x := by
  -- `TauCeti.TopRep.comp_apply` is stated at the carrier of a `TauCeti.TopRep` object, while the
  -- carrier of `TauCeti.ofDiscreteModule` is the field projection `.V` of a structure literal, so
  -- the rule does not match the composite; `change` exposes it.
  rw [kummerCoeffIsoTrivialF2_hom]
  change eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K))
    ((kummerCoeffToTrivialF2 K) x) = kummerCoeffEquiv K x
  rw [kummerCoeffToTrivialF2_apply, eqToHom_ofDiscreteModule_trivialF2_apply]

/-- **The inverse isomorphism reads on carriers as the inverse value dictionary.** -/
@[simp]
theorem kummerCoeffIsoTrivialF2_inv_apply (b : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    (kummerCoeffIsoTrivialF2 K).inv b = (kummerCoeffEquiv K).symm b := by
  -- As above: `change` exposes the composite of the two inverses at the carrier.
  change (ofDiscreteModuleIso (kummerCoeffEquiv K).toIntLinearEquiv
      (kummerCoeffEquiv_equivariant K)).inv.hom
    ((eqToIso (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K))).inv b)
    = (kummerCoeffEquiv K).symm b
  rw [eqToIso.inv, eqToHom_ofDiscreteModule_trivialF2_symm_apply]
  exact ofDiscreteModuleIso_inv_hom_apply _ _ _

/-! ### The Kummer class of a unit -/

/-- The degree-one map on continuous cohomology induced by the coefficient isomorphism
`TauCeti.kummerCoeffIsoTrivialF2`, read off the image isomorphism the continuous-cohomology functor
`TauCeti.ContinuousCohomology.continuousCohomologyFunctor` assigns to it. -/
noncomputable def kummerCohomMap :
    continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2)) ⟶
      continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 1).mapIso
    (kummerCoeffIsoTrivialF2 K) |>.hom

/-- **`TauCeti.kummerCohomMap` factors through the coefficient map of the dictionary**: it is
the coefficient map of `TauCeti.kummerCoeffToTrivialF2` followed by the transport of
`TauCeti.ofDiscreteModule_trivialF2` on degree-one continuous cohomology. -/
private theorem kummerCohomMap_eq_coeffMap_comp :
    kummerCohomMap K =
      ContinuousCohomology.coeffMap (kummerCoeffToTrivialF2 K) 1 ≫
        eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K))) := by
  rw [kummerCohomMap, Functor.mapIso_hom,
    ContinuousCohomology.continuousCohomologyFunctor_map, kummerCoeffIsoTrivialF2_hom,
    ContinuousCohomology.coeffMap_comp, ContinuousCohomology.coeffMap_eqToHom]

/-- **The coefficient isomorphism read on degree-one continuous cohomology, as an equivalence of
additive groups**: the equivalence of additive groups that
`TauCeti.ContinuousCohomology.continuousCohomologyFunctor` assigns to
`TauCeti.kummerCoeffIsoTrivialF2`, read off the image isomorphism's own equivalence API rather
than reassembled from the bijectivity of the morphism `TauCeti.kummerCohomMap`. -/
private noncomputable def kummerCohomAddEquiv :
    continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2)) ≃+
      continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 1).mapIso
    (kummerCoeffIsoTrivialF2 K) |>.toContinuousLinearEquiv.toAddEquiv

/-- The degree-one coefficient isomorphism applies as the degree-one map it is read off. -/
@[simp]
private theorem kummerCohomAddEquiv_apply
    (y : continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2))) :
    kummerCohomAddEquiv K y = (kummerCohomMap K).hom y :=
  rfl

variable {K}

/-- **The Kummer class** `(a) ∈ H¹(G_K, 𝔽₂)` of a unit `a`: the canonical Kummer map
`TauCeti.kummerMapCanonical` at `n = 2`, read through the coefficient-object isomorphism
`TauCeti.kummerCoeffIsoTrivialF2`. -/
noncomputable def kummerClass (a : Kˣ) :
    continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (kummerCohomMap K).hom
    (Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_of_invertible (2 : K)) a))

/-- The Kummer class is the canonical Kummer map followed by the degree-one coefficient
map from roots of unity to trivial `𝔽₂` coefficients. -/
theorem kummerClass_def (a : Kˣ) :
    kummerClass a = (kummerCohomMap K).hom
      (Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_of_invertible (2 : K)) a)) :=
  (rfl)

variable (K)

/-- **The Kummer class of `1` is the neutral element**: `TauCeti.kummerClass` is a homomorphism
from `Kˣ` into `H¹(G_K, 𝔽₂)` written additively, paired with the multiplication law
`TauCeti.kummerClass_mul`. -/
@[simp]
theorem kummerClass_one : kummerClass (1 : Kˣ) = 0 := by
  simp [kummerClass]

/-- **The Kummer class of a product is the sum of the two Kummer classes**: the
multiplicative-to-additive law of the Kummer class, its identity law being
`TauCeti.kummerClass_one`. -/
@[simp]
theorem kummerClass_mul (a b : Kˣ) :
    kummerClass (a * b) = kummerClass a + kummerClass b := by
  simp [kummerClass]

local instance : ContinuousSMul (AbsoluteGaloisGroup K)
    (trivialF2 (AbsoluteGaloisGroup K)).V :=
  (isSmoothDiscrete_trivialF2 (AbsoluteGaloisGroup K)).continuousSMul

/-- Equality of units of a separable closure is decidable, classically. This is what lets the
value formula `TauCeti.kummerCocycleModTwo_apply` be stated with an `if`; it carries no
mathematical content and is local to this file. -/
-- Named rather than anonymous: Lean's generated name for the anonymous form carries an underscore
-- (`instDecidableEqUnitsSeparableClosure_tauCeti`), which the `defsWithUnderscore` linter rejects.
local instance instDecidableEqUnitsSeparableClosure : DecidableEq (SeparableClosure K)ˣ :=
  Classical.decEq _

/-- **The `𝔽₂`-valued Kummer cocycle of a chosen square root.** If `α² = a`, this is
the ratio cocycle `g ↦ g • α / α`, transported from `μ₂` to the trivial `𝔽₂` coefficient
module. Its decoded values are computed by `TauCeti.kummerCocycleModTwo_apply`. -/
noncomputable def kummerCocycleModTwo {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    Z1 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V :=
    cocyclesMap1 (AbsoluteGaloisGroup K) (KummerCoeff K 2)
    (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V
    (ContinuousMonoidHom.id _) (kummerCoeffEquiv K).toAddMonoidHom
    continuous_of_discreteTopology (fun g x => by simp [kummerCoeffEquiv_apply])
    ⟨kummerCocycle hα, kummerCocycle_mem_Z1 hα⟩

/-- **The value of the Kummer cocycle in `ZMod 2`.** The Kummer ratio `g • α / α` of a chosen
square root `α` is `0` when `g` fixes `α` and `1` when it exchanges the two square roots. -/
@[simp]
theorem mu2EquivZMod2_kummerCocycle {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (g : AbsoluteGaloisGroup K) :
    mu2EquivZMod2 K (kummerCocycle hα g) = if g • α = α then 0 else 1 := by
  split_ifs with hfix
  · have hc : kummerCocycle hα g = (0 : KummerCoeff K 2) := by
      refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
      simp [hfix]
    simp [hc]
  · have hc : kummerCocycle hα g = mu2NegOne := by
      rcases eq_zero_or_eq_mu2NegOne (kummerCocycle hα g) with hz | hz
      · exfalso
        apply hfix
        have hz' := congrArg
          (fun z : KummerCoeff K 2 => (z.toMul : (SeparableClosure K)ˣ)) hz
        exact mul_inv_eq_one.mp <|
          (toMul_kummerCocycle hα g).symm.trans (by simpa using hz')
      · exact hz
    simp [hc]

/-- **The square-root formula for the mod-two Kummer cocycle.** Its value at `g` is `0` when
`g` fixes the chosen square root and `1` when it exchanges the two square roots. -/
@[simp]
theorem kummerCocycleModTwo_apply {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (g : AbsoluteGaloisGroup K) :
    trivialF2Equiv (AbsoluteGaloisGroup K)
        ((kummerCocycleModTwo K hα : _ → _) g) =
      if g • α = α then 0 else 1 := by
  rw [kummerCocycleModTwo, cocyclesMap1_apply, ContinuousMonoidHom.coe_id, id_eq]
  -- The coefficient map inside `cocyclesMap1` is stored as an additive homomorphism; expose
  -- its underlying equivalence application so the two value dictionaries can cancel.
  change trivialF2Equiv (AbsoluteGaloisGroup K)
    (kummerCoeffEquiv K (kummerCocycle hα g)) = _
  rw [kummerCoeffEquiv_apply, AddEquiv.apply_symm_apply, mu2EquivZMod2_kummerCocycle]

/-- The explicit cohomology class of the mod-two Kummer cocycle attached to a chosen square
root. It is independent of that choice because it is the coefficient transport of
`TauCeti.kummerCocycleClass`. -/
noncomputable def kummerCocycleModTwoClass {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    H1 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V :=
  kummerCocycleModTwo K hα

/-- The explicit mod-two Kummer class is the class of the explicit mod-two Kummer cocycle. -/
theorem kummerCocycleModTwoClass_def {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerCocycleModTwoClass K hα =
      (kummerCocycleModTwo K hα :
        H1 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V) :=
  (rfl)

/-- The explicit mod-two cocycle class is the generic Kummer cocycle class transported along
the coefficient equivalence `μ₂ ≃ 𝔽₂`. -/
theorem kummerCocycleModTwoClass_eq_explicitCoeff1Equiv {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerCocycleModTwoClass K hα =
      explicitCoeff1Equiv (AbsoluteGaloisGroup K) (KummerCoeff K 2)
        (kummerCoeffEquiv K) continuous_of_discreteTopology continuous_of_discreteTopology
        (fun g x => by simp [kummerCoeffEquiv_apply]) (kummerCocycleClass hα) := by
  rw [kummerCocycleModTwoClass, kummerCocycleClass_def]
  -- Both sides are quotient classes. Exposing their cocycle representatives reduces the
  -- comparison theorem to `explicitCoeff1Equiv_mk`.
  change (kummerCocycleModTwo K hα :
      H1 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V) =
    explicitCoeff1Equiv (AbsoluteGaloisGroup K) (KummerCoeff K 2)
      (kummerCoeffEquiv K) continuous_of_discreteTopology continuous_of_discreteTopology
      (fun g x => by simp [kummerCoeffEquiv_apply])
      ((⟨kummerCocycle hα, kummerCocycle_mem_Z1 hα⟩ :
        Z1 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
          H1 (AbsoluteGaloisGroup K) (KummerCoeff K 2))
  rw [explicitCoeff1Equiv_mk, kummerCocycleModTwo]
  -- Compare the two coefficient pushforwards of the cocycle pointwise: by `cocyclesMap1_apply`,
  -- each is its coefficient map applied to the Kummer cocycle, and the equivariant repackaging
  -- of `kummerCoeffEquiv K` built by `explicitCoeff1Equiv` has `kummerCoeffEquiv K` as its
  -- underlying function.
  refine congrArg _ (Subtype.ext (funext fun g ↦ ?_))
  rw [cocyclesMap1_apply]
  refine Eq.trans ?_ (cocyclesMap1_apply _ _ _ _ _ _ _ _ _ g).symm
  simp only [DistribMulActionHom.coe_fn_coe, ← DistribMulActionHom.toFun_eq_coe,
    ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]

/-- The explicit mod-two Kummer cocycle class does not depend on the chosen square root. -/
theorem kummerCocycleModTwoClass_congr {a : Kˣ} {α β : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (hβ : β ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerCocycleModTwoClass K hα = kummerCocycleModTwoClass K hβ := by
  rw [kummerCocycleModTwoClass_eq_explicitCoeff1Equiv,
    kummerCocycleModTwoClass_eq_explicitCoeff1Equiv,
    kummerCocycleClass_congr hα hβ]

/-- **The Kummer class of a unit vanishes exactly at the squares in `Kˣ`.** -/
@[simp]
theorem kummerClass_eq_zero_iff_square {a : Kˣ} :
    kummerClass a = 0 ↔ a ∈ Subgroup.square Kˣ := by
  constructor
  · intro hz
    -- `kummerClass` is the canonical Kummer map read through the degree-one coefficient map, so
    -- injectivity of that map, read off `TauCeti.kummerCohomAddEquiv`, reads `hz` back as a
    -- vanishing canonical Kummer map.
    have hzero : (kummerCohomMap K).hom
        (Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_of_invertible (2 : K)) a)) = 0 :=
      by simpa only [kummerClass] using hz
    have hz' : Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_of_invertible (2 : K)) a)
        = 0 :=
      (kummerCohomAddEquiv K).injective <|
        by simpa only [kummerCohomAddEquiv_apply, map_zero] using hzero
    have hz'' : Multiplicative.toAdd (kummerMap K 2 (isUnit_of_invertible (2 : K)) a) = 0 := by
      -- The degree-one comparison sends the explicit Kummer map to the canonical one, and the
      -- comparison is an additive equivalence, so it is injective.
      have h0 := (explicitIso_kummerMap K 2 (isUnit_of_invertible (2 : K)) a).symm.trans hz'
      refine (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K)
        (KummerCoeff K 2)).injective
          (a₁ := Multiplicative.toAdd (kummerMap K 2 (isUnit_of_invertible (2 : K)) a)) (a₂ := 0) ?_
      rw [h0, map_zero]
    have hone : kummerMap K 2 (isUnit_of_invertible (2 : K)) a = 1 :=
      toAdd_eq_zero.mp hz''
    obtain ⟨r, hr⟩ := (kummerMap_eq_one_iff (isUnit_of_invertible (2 : K)) a).mp hone
    exact Subgroup.mem_square.mpr ⟨r, by rw [← hr, pow_two]⟩
  · intro ha
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

/-- **The degree-one comparison carries the coefficient dictionary to `TauCeti.kummerCohomMap`.**
Reading the explicit coefficient equivalence `μ₂ ≃ 𝔽₂` on explicit `H¹` and then comparing with
canonical continuous cohomology is the same as comparing first and then applying the map that
`TauCeti.kummerCoeffIsoTrivialF2` induces; the trailing transport is the one of
`TauCeti.ofDiscreteModule_trivialF2`, which `kummerCoeffIsoTrivialF2` absorbs into its target. -/
theorem kummerCohomMap_explicitH1 (x : H1 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
    (kummerCohomMap K).hom
        (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (KummerCoeff K 2) x) =
      (eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)))).hom
        (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K)
          (trivialF2 (AbsoluteGaloisGroup K)).V
          (explicitCoeff1Equiv (AbsoluteGaloisGroup K) (KummerCoeff K 2) (kummerCoeffEquiv K)
            continuous_of_discreteTopology continuous_of_discreteTopology
            (kummerCoeffEquiv_equivariant K) x)) := by
  rw [kummerCohomMap_eq_coeffMap_comp, ConcreteCategory.comp_apply]
  refine congrArg _ ?_
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.id (AbsoluteGaloisGroup K) :
        AbsoluteGaloisGroup K →* AbsoluteGaloisGroup K)
      (kummerCoeffEquiv K).toAddMonoidHom.toIntLinearMap
        (fun g m ↦ kummerCoeffEquiv_equivariant K g m) = kummerCoeffToTrivialF2 K :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [ContinuousCohomology.coeffMap_def, ← hpair,
    explicitH1AddEquivContinuousCohomology_map (AbsoluteGaloisGroup K) (KummerCoeff K 2)
      (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V
      (ContinuousMonoidHom.id _) (kummerCoeffEquiv K).toAddMonoidHom
      (fun g m ↦ kummerCoeffEquiv_equivariant K g m) x]
  refine congrArg _ ?_
  -- The coefficient equivalence is the coefficient map of its forward equivariant homomorphism,
  -- and a coefficient map is the compatible-pair pullback along the identity of the group, which
  -- is what the left-hand side names directly.
  exact ((explicitCoeff1Equiv_apply (AbsoluteGaloisGroup K) (KummerCoeff K 2) (kummerCoeffEquiv K)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (kummerCoeffEquiv_equivariant K) x).trans
      (DFunLike.congr_fun (explicitCoeff1_eq_explicitMap1 (AbsoluteGaloisGroup K)
        (KummerCoeff K 2) { (kummerCoeffEquiv K).toAddMonoidHom with
          map_smul' := kummerCoeffEquiv_equivariant K } continuous_of_discreteTopology) x)).symm

/-- **The mod-two Kummer class is the explicit mod-two cocycle class of any square root.**
If `α² = a`, the class `TauCeti.kummerCocycleModTwoClass` of the `𝔽₂`-valued cocycle
`g ↦ g • α / α` becomes the Kummer class `(a)` under the degree-one comparison with canonical
continuous cohomology, followed by the transport of `TauCeti.ofDiscreteModule_trivialF2` that
identifies the coefficient object of the comparison with `TauCeti.trivialF2` itself. -/
theorem kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq (a : Kˣ) (α : (SeparableClosure K)ˣ)
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    kummerClass a =
      (eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)))).hom
        (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K)
          (trivialF2 (AbsoluteGaloisGroup K)).V (kummerCocycleModTwoClass K hα)) := by
  rw [kummerClass, explicitIso_kummerMap,
    kummerMap_eq_kummerCocycleClass (isUnit_of_invertible (2 : K)) hα,
    kummerCocycleModTwoClass_eq_explicitCoeff1Equiv]
  exact kummerCohomMap_explicitH1 K (kummerCocycleClass hα)

/-! ### The Kummer isomorphism on square classes -/

/-- **The literal square-class quotient is the power-class quotient at `n = 2`**: the subgroup of
`n`th powers is at `n = 2` the subgroup of squares, so `TauCeti.MultiplicativeSquareClassGroup K`,
the literal quotient `Kˣ ⧸ (Kˣ)²`, is the quotient `TauCeti.powerClassQuotient Kˣ 2` that
`TauCeti.kummerIso` is stated on. The two subgroups are compared through their two descriptions of
their elements, the squares and the `n`th powers at `n = 2` (`TauCeti.mem_powerSubgroup_iff`). -/
private noncomputable def squareClassQuotientEquiv :
    MultiplicativeSquareClassGroup K ≃* powerClassQuotient Kˣ 2 :=
  QuotientGroup.quotientMulEquivOfEq (by
    -- The two subgroups are identified through the two descriptions of their elements, the
    -- squares and the `n`th powers at `n = 2` (`TauCeti.mem_powerSubgroup_iff`).
    ext g
    rw [Subgroup.mem_square, mem_powerSubgroup_iff]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, by rw [pow_two]⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [← hr, pow_two]⟩)

omit [Invertible (2 : K)] in
/-- The literal square-class quotient is the identity on representatives: the application rule of
`TauCeti.squareClassQuotientEquiv` on the class of a unit, which is how `TauCeti.kummerIso` is
read on a representative. -/
@[simp]
private theorem squareClassQuotientEquiv_mk (a : Kˣ) :
    squareClassQuotientEquiv K (QuotientGroup.mk a) = QuotientGroup.mk a :=
  QuotientGroup.quotientMulEquivOfEq_mk _ a

omit [Invertible (2 : K)] in
/-- The canonical equivalence reads the square class of `a` back to the class of `a` in
`TauCeti.MultiplicativeSquareClassGroup K`: the application rule of
`TauCeti.multiplicativeSquareClassEquiv` on its own value, in the direction that leaves the additive
square-class group for the literal quotient. -/
@[simp]
private theorem multiplicativeSquareClassEquiv_symm_mk (a : Kˣ) :
    (multiplicativeSquareClassEquiv (K := K)).symm (Multiplicative.ofAdd (squareClass a))
      = QuotientGroup.mk a := by
  rw [← multiplicativeSquareClassEquiv_mk a]
  exact MulEquiv.symm_apply_apply _ _

/-- **The Kummer isomorphism on square classes**, into the explicit `H¹(G_K, μ₂)`: the generic
Kummer isomorphism `TauCeti.kummerIso` at `n = 2`, whose domain is `Kˣ ⧸ (Kˣ)ⁿ`, read on the
square-class group `TauCeti.SquareClassGroup K` through the two identifications
`TauCeti.multiplicativeSquareClassEquiv` and `TauCeti.squareClassQuotientEquiv` above. -/
private noncomputable def kummerSquareClassEquivH1 :
    SquareClassGroup K ≃+ H1 (AbsoluteGaloisGroup K) (KummerCoeff K 2) :=
  (AddEquiv.additiveMultiplicative (G := SquareClassGroup K)).symm.trans
    (MulEquiv.toAdditiveLeft
      ((multiplicativeSquareClassEquiv (K := K)).symm.trans
        ((squareClassQuotientEquiv K).trans (kummerIso K 2 (isUnit_of_invertible (2 : K))))))

/-- **The Kummer isomorphism on square classes sends the square class of `a` to the Kummer class
`(a)`**: the isomorphism read on a representative `a`, which is the only statement about it needed
downstream. -/
@[simp]
private theorem kummerSquareClassEquivH1_squareClass (a : Kˣ) :
    kummerSquareClassEquivH1 K (squareClass a)
      = Multiplicative.toAdd (kummerMap K 2 (isUnit_of_invertible (2 : K)) a) := by
  -- Every layer of the composite is read off its application rule: the additive presentation of
  -- the square-class group, the canonical equivalence, the literal quotient, and the Kummer
  -- isomorphism on a representative `a` (`TauCeti.kummerIso_apply` and
  -- `TauCeti.kummerClassMap_mk`). The single named rewrite is the rule that removes the generated
  -- additive and multiplicative type tags.
  simp [kummerSquareClassEquivH1, AddEquiv.toMultiplicativeRight_symm_apply_apply,
    multiplicativeSquareClassEquiv_symm_mk, squareClassQuotientEquiv_mk]

/-- **The Kummer isomorphism on the square classes** `Kˣ ⧸ (Kˣ)² ≃+ H¹(G_K, 𝔽₂)`: the square class
of a unit `a` is sent to the Kummer class `(a)`. The square-class side is the square-class group
`Kˣ ⧸ (Kˣ)²`, that is `TauCeti.SquareClassGroup K`, in which the class of `a` is
`TauCeti.squareClass a`. -/
noncomputable def kummerSquareClassEquiv :
    SquareClassGroup K ≃+ continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (kummerSquareClassEquivH1 K).trans
    ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (KummerCoeff K 2)).trans
      (kummerCohomAddEquiv K))

variable {K}

/-- The Kummer isomorphism on square classes sends the square class of `a` to the Kummer class
`(a)`, which is the statement that identifies its two sides. -/
@[simp]
theorem kummerSquareClassEquiv_squareClass (a : Kˣ) :
    kummerSquareClassEquiv K (squareClass a) = kummerClass a := by
  -- Both sides are the same composite read on the same input: the explicit `H¹` isomorphism on the
  -- square class of `a` (`TauCeti.kummerSquareClassEquivH1_squareClass`), the degree-one
  -- coefficient map, and the canonical Kummer class of `a`, which
  -- `TauCeti.explicitIso_kummerMap` reads as the explicit one.
  simp [kummerSquareClassEquiv, kummerClass, explicitIso_kummerMap]

/-- **Two units have the same Kummer class exactly when their product is a square**: the
quotient-free reading of equality of Kummer classes, through `TauCeti.kummerSquareClassEquiv`. -/
theorem kummerClass_eq_kummerClass_iff_isSquare_mul (a b : Kˣ) :
    kummerClass a = kummerClass b ↔ IsSquare (a * b) := by
  rw [← kummerSquareClassEquiv_squareClass, ← kummerSquareClassEquiv_squareClass,
    EmbeddingLike.apply_eq_iff_eq, squareClass_eq_iff_isSquare_mul]

end TauCeti
