/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Smooth.Field
public import TauCeti.FieldTheory.Frobenius.Range
public import TauCeti.RingTheory.Ideal.Quotient.SquareZero

/-!
# Extensions of perfect fields are formally smooth

Every field extension `L / K` of a perfect field `K` is formally smooth: an algebra map
`L →ₐ[K] B ⧸ I` lifts to `L →ₐ[K] B` along every square-zero ideal `I`. Mathlib proves this for
`L / K` essentially of finite type (`Algebra.FormallySmooth.of_perfectField`), through a separating
transcendence basis. A general extension need not have one: `𝔽_p(t ^ (1 / p ^ ∞))` is not
separably generated over `𝔽_p`. This file removes the finiteness hypothesis.

In characteristic zero a transcendence basis is still separating, and Mathlib's
`Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` applies. In characteristic `p` the
proof uses the Frobenius map instead. Since `I ^ 2 = 0` and `p = 0` in `B`, the `p`-th power of a
lift of `z ∈ B ⧸ I` does not depend on the lift. This gives a ring homomorphism `B ⧸ I → B`, and
composed with the given map, the only possible lift `ψ` on the subfield `L ^ p`. Zorn's lemma
gives a maximal lift extending it. It is defined on all of `L`: if `a ∉ M`, then `a ^ p ∈ M` and
`X ^ p - a ^ p` is the minimal polynomial of `a` over `M`. Any lift `b` of the image of `a` has
`b ^ p = ψ(a ^ p)`, so `a ↦ b` extends the lift to `M(a)`.

This is the input of Cohen's structure theorem for complete local rings in equal characteristic,
which constructs coefficient fields by lifting the identity of the residue field.

## Main results

* `TauCeti.formallySmooth_of_perfectField`: every field extension of a perfect field is formally
  smooth.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Première partie, Publ. Math. IHÉS 20
  (1964), Chapitre 0, Théorème 19.6.1.
* H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1986, Theorem 26.9 and
  Section 28.

The chain argument for partial lifts follows Mathlib's `IntermediateField.Lifts`, whose target is
a field, adapted here to a ring target.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

section PartialLift

variable (K L B : Type*) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]

/-- A `K`-algebra map from an intermediate field of `L / K` into `B`. -/
private structure PartialLift where
  /-- The domain of the partial lift. -/
  carrier : IntermediateField K L
  /-- The partial lift. -/
  emb : carrier →ₐ[K] B

variable {K L B}

namespace PartialLift

/-- A partial lift is below another one when the latter extends it. -/
private instance : Preorder (PartialLift K L B) where
  le φ₁ φ₂ := ∃ h : φ₁.carrier ≤ φ₂.carrier, ∀ x, φ₂.emb (inclusion h x) = φ₁.emb x
  le_refl φ := ⟨le_rfl, by simp⟩
  le_trans φ₁ φ₂ φ₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ ↦ ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃, h₂₃', h₁₂']

private theorem directed_carrier {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c) :
    Directed (· ≤ ·) fun i : c ↦ i.val.carrier :=
  hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1

/-- The members of a chain of partial lifts agree on the intersections of their domains. -/
private theorem emb_compat {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c) (i j : c)
    (h : i.val.carrier.toSubalgebra ≤ j.val.carrier.toSubalgebra) :
    i.val.emb = j.val.emb.comp (Subalgebra.inclusion h) :=
  AlgHom.ext fun x ↦ (hc.total i.2 j.2).elim (fun hij ↦ (hij.snd x).symm) fun hji ↦ by
    rw [AlgHom.comp_apply, ← inclusion, ← hji.snd (inclusion h x), inclusion_inclusion,
      inclusion_self, AlgHom.id_apply x]

/-- The union of a nonempty chain of partial lifts. -/
private noncomputable def union (c : Set (PartialLift K L B)) (hc : IsChain (· ≤ ·) c)
    [Nonempty c] : PartialLift K L B :=
  ⟨⨆ i : c, i.val.carrier, Subalgebra.iSupLift (fun i : c ↦ i.val.carrier.toSubalgebra)
    (directed_carrier hc) (fun i ↦ i.val.emb) (emb_compat hc)
    (⨆ i : c, i.val.carrier).toSubalgebra (toSubalgebra_iSup_of_directed (directed_carrier hc)).le⟩

/-- On the domain of a member of the chain, the union of the chain is that member. -/
private theorem union_emb_of_mem {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c)
    [Nonempty c] (x : (union c hc).carrier) {φ : PartialLift K L B} (hφ : φ ∈ c)
    (hx : (x : L) ∈ φ.carrier) : (union c hc).emb x = φ.emb ⟨x, hx⟩ :=
  Subalgebra.iSupLift_of_mem (K := fun i : c ↦ i.val.carrier.toSubalgebra)
    (dir := directed_carrier hc) (hf := emb_compat hc) (i := ⟨φ, hφ⟩) x hx

private theorem le_union {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c) [Nonempty c]
    {φ : PartialLift K L B} (hφ : φ ∈ c) : φ ≤ union c hc :=
  ⟨le_iSup (fun i : c ↦ i.val.carrier) ⟨φ, hφ⟩, fun x ↦ union_emb_of_mem hc _ hφ x.2⟩

/-- Every point of the union of a chain lies in the domain of one of its members. -/
private theorem exists_mem_of_mem_union {c : Set (PartialLift K L B)} (hc : IsChain (· ≤ ·) c)
    [Nonempty c] (x : (union c hc).carrier) : ∃ φ ∈ c, (x : L) ∈ φ.carrier := by
  have hx : (x : L) ∈ ⋃ i : c, (i.val.carrier : Set L) := by
    rw [← coe_iSup_of_directed (directed_carrier hc)]
    exact x.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, i.2, hi⟩

/-- A partial lift defined at `a ^ p`, but not at `a`, extends to `a`, with any value `b` such
that `b ^ p` is the value at `a ^ p`. -/
private theorem exists_le_of_pow_mem (p : ℕ) [Fact p.Prime] [CharP L p] (φ : PartialLift K L B)
    {a : L} (ha : a ∉ φ.carrier) (hap : a ^ p ∈ φ.carrier) {b : B}
    (hb : φ.emb ⟨a ^ p, hap⟩ = b ^ p) :
    ∃ φ' : PartialLift K L B, φ ≤ φ' ∧ φ'.carrier = φ.carrier⟮a⟯.restrictScalars K ∧
      ∃ h : a ∈ φ'.carrier, φ'.emb ⟨a, h⟩ = b := by
  set M := φ.carrier
  -- `X ^ p - a ^ p` is the minimal polynomial of `a` over `M`
  have hirr : Irreducible (X ^ p - C (⟨a ^ p, hap⟩ : M)) :=
    X_pow_sub_C_irreducible_of_prime Fact.out fun c hc ↦ ha <| by
      have hc' : (c : L) ^ p = a ^ p := congrArg Subtype.val hc
      rw [← frobenius_def p, ← frobenius_def p] at hc'
      exact frobenius_inj L p hc' ▸ c.2
  have hroot : aeval a (X ^ p - C (⟨a ^ p, hap⟩ : M)) = 0 := by simp
  have hint : IsIntegral M a := ⟨_, monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, by
    rwa [← aeval_def]⟩
  have hmin : minpoly M a = X ^ p - C (⟨a ^ p, hap⟩ : M) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot
      (monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero)).symm
  let : Algebra M B := φ.emb.toRingHom.toAlgebra
  let carrier := M⟮a⟯.restrictScalars K
  let : Algebra M carrier := M⟮a⟯.toSubalgebra.algebra
  have hb' : aeval b (minpoly M (adjoin.powerBasis hint).gen) = 0 := by
    rw [adjoin.powerBasis_gen, minpoly_gen, hmin, map_sub, map_pow, aeval_X, aeval_C]
    simp [RingHom.algebraMap_toAlgebra, ← hb]
  let σ : carrier →ₐ[M] B := (adjoin.powerBasis hint).lift b hb'
  have : IsScalarTower K M carrier := IsScalarTower.of_algebraMap_eq fun c ↦
    Subtype.ext (IsScalarTower.algebraMap_apply K M L c)
  refine ⟨⟨carrier, (algHomEquivSigma (A := K) (B := M) (C := carrier) (D := B)).symm ⟨φ.emb, σ⟩⟩,
    ⟨fun z hz ↦ IntermediateField.algebraMap_mem M⟮a⟯ ⟨z, hz⟩, σ.commutes⟩, rfl,
    mem_adjoin_simple_self M a, ?_⟩
  exact (adjoin.powerBasis hint).lift_gen b hb'

/-- A partial lift extending a lift `φ` to the adjunction of `a` lifts `f` if `φ` does and the
value at `a` lifts `f a`. -/
private theorem mk_emb_of_le {I : Ideal B} {f : L →ₐ[K] B ⧸ I} {φ φ' : PartialLift K L B}
    (hφφ' : φ ≤ φ') {a : L} (hcarrier : φ'.carrier = φ.carrier⟮a⟯.restrictScalars K)
    (ha : a ∈ φ'.carrier)
    (hφa : Ideal.Quotient.mk I (φ'.emb ⟨a, ha⟩) = f a)
    (hφ : ∀ x, Ideal.Quotient.mk I (φ.emb x) = f x) (x : φ'.carrier) :
    Ideal.Quotient.mk I (φ'.emb x) = f x := by
  have hS : φ'.carrier = adjoin K (φ.carrier ∪ {a}) := by rw [hcarrier, restrictScalars_adjoin]
  have h := algHom_ext_of_eq_adjoin K hS (φ₁ := (Ideal.Quotient.mkₐ K I).comp φ'.emb)
    (φ₂ := f.comp φ'.carrier.val) fun y hy ↦ by
      rcases hy with hy | rfl
      · exact (congrArg (Ideal.Quotient.mk I) (hφφ'.2 ⟨y, hy⟩)).trans (hφ ⟨y, hy⟩)
      · simpa using hφa
  exact AlgHom.congr_fun h x

end PartialLift

end PartialLift

section CharP

variable (p : ℕ) [Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharP K p] [PerfectField K]
variable {B : Type*} [CommRing B] [Algebra K B] (hpB : (p : B) = 0) {I : Ideal B}
  (hI : I ^ 2 = ⊥)

/-- The only possible lift of `f` on the field `L ^ p`, as a ring homomorphism: it sends `x ^ p`
to the `p`-th power of a lift of `f x`. -/
private noncomputable def powFieldRingHom (f : L →ₐ[K] B ⧸ I) : frobeniusPowers K L p 1 →+* B :=
  ((Ideal.Quotient.powLift p hpB hI).comp f.toRingHom).comp
    (iterateFrobeniusEquivPowers K L p 1).symm.toRingHom

private theorem powFieldRingHom_apply (f : L →ₐ[K] B ⧸ I) (x : L) :
    powFieldRingHom p hpB hI f (iterateFrobeniusEquivPowers K L p 1 x) =
      Ideal.Quotient.powLift p hpB hI (f x) := by
  simp [powFieldRingHom]

/-- The only possible lift of `f` on the field `L ^ p`. -/
private noncomputable def powFieldLift (f : L →ₐ[K] B ⧸ I) : frobeniusPowers K L p 1 →ₐ[K] B :=
  { powFieldRingHom p hpB hI f with
    commutes' c := by
      obtain ⟨d, rfl⟩ := (iterateFrobeniusEquiv K p 1).surjective c
      -- the underlying function of `powFieldLift` is `powFieldRingHom`
      change powFieldRingHom p hpB hI f _ = _
      -- write the constant as a `p`-th power of a constant of `L`, then compute
      rw [← iterateFrobeniusEquivPowers_algebraMap]
      simp [-iterateFrobeniusEquivPowers_algebraMap, powFieldRingHom_apply,
        ← Ideal.Quotient.mk_algebraMap, frobenius_def] }

private theorem powFieldLift_apply (f : L →ₐ[K] B ⧸ I) (x : L) :
    powFieldLift p hpB hI f (iterateFrobeniusEquivPowers K L p 1 x) =
      Ideal.Quotient.powLift p hpB hI (f x) :=
  powFieldRingHom_apply p hpB hI f x

/-- The lift of `f` on `L ^ p` lifts `f`. -/
private theorem mk_powFieldLift (f : L →ₐ[K] B ⧸ I) (y : frobeniusPowers K L p 1) :
    Ideal.Quotient.mk I (powFieldLift p hpB hI f y) = f y := by
  obtain ⟨x, rfl⟩ := (iterateFrobeniusEquivPowers K L p 1).surjective y
  simp [powFieldLift_apply]

open PartialLift in
include hpB hI in
/-- **In characteristic `p`, a map of a field `L` over a perfect field `K` into `B ⧸ I` lifts to
`B` along a square-zero ideal `I`.** -/
private theorem exists_comp_eq_of_charP [CharP L p] (f : L →ₐ[K] B ⧸ I) :
    ∃ g : L →ₐ[K] B, (Ideal.Quotient.mkₐ K I).comp g = f := by
  -- the partial lifts of `f` which extend its lift on `L ^ p`
  let base : PartialLift K L B := ⟨frobeniusPowers K L p 1, powFieldLift p hpB hI f⟩
  let S : Set (PartialLift K L B) :=
    {φ | base ≤ φ ∧ ∀ x, Ideal.Quotient.mk I (φ.emb x) = f x}
  obtain ⟨φ, -, hφ⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy ↦ by
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    refine ⟨union c hc, ⟨(hcS hy).1.trans (le_union hc hy), fun x ↦ ?_⟩,
      fun z hz ↦ le_union hc hz⟩
    obtain ⟨ψ, hψ, hx⟩ := exists_mem_of_mem_union hc x
    rw [union_emb_of_mem hc x hψ hx]
    exact (hcS hψ).2 _) base ⟨le_rfl, mk_powFieldLift p hpB hI f⟩
  -- a maximal partial lift is defined everywhere
  have htop : φ.carrier = ⊤ := by
    refine eq_top_iff.mpr fun a _ ↦ by_contra fun ha ↦ ?_
    let ap := iterateFrobeniusEquivPowers K L p 1 a
    have hap : a ^ p ∈ φ.carrier := by simpa [ap] using hφ.prop.1.1 ap.2
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f a)
    have hbp : φ.emb ⟨a ^ p, hap⟩ = b ^ p := by
      have h : (⟨a ^ p, hap⟩ : φ.carrier) = inclusion hφ.prop.1.1 ap := Subtype.ext (by simp [ap])
      rw [h, hφ.prop.1.2, powFieldLift_apply, ← hb, Ideal.Quotient.powLift_mk]
    obtain ⟨φ', hφφ', hcarrier, ha', hφ'a⟩ := PartialLift.exists_le_of_pow_mem p φ ha hap hbp
    have hφ' : φ' ∈ S := ⟨hφ.prop.1.trans hφφ',
      mk_emb_of_le hφφ' hcarrier ha' (by rw [hφ'a, hb]) hφ.prop.2⟩
    exact ha ((hφ.2 hφ' hφφ').1 ha')
  refine ⟨φ.emb.comp ((equivOfEq htop).trans topEquiv).symm.toAlgHom, AlgHom.ext fun x ↦ ?_⟩
  simpa using hφ.prop.2 (((equivOfEq htop).trans topEquiv).symm x)

end CharP

/-- **Every field extension of a perfect field is formally smooth**: a `K`-algebra map from `L` to
`B ⧸ I`, for a square-zero ideal `I`, lifts to `B`. No finiteness hypothesis on `L / K` is needed,
unlike for Mathlib's `Algebra.FormallySmooth.of_perfectField`. -/
instance (priority := low) formallySmooth_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [PerfectField K] : Algebra.FormallySmooth K L := by
  obtain _ | ⟨p, hp, hpK⟩ := CharP.exists' K
  · -- in characteristic zero, every transcendence basis is separating
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
    have := hs.isAlgebraic_field
    have := charZero_of_injective_algebraMap (algebraMap K L).injective
    have := Algebra.IsAlgebraic.isSeparable_of_perfectField
      (K := IntermediateField.adjoin K (Set.range ((↑) : s → L))) (L := L)
    exact .of_algebraicIndependent_of_isSeparable hs.1
  · have : CharP L p := .of_ringHom_of_ne_zero (algebraMap K L) p hp.out.ne_zero
    refine .of_comp_surjective fun B _ _ I hI f ↦ exists_comp_eq_of_charP p ?_ hI f
    rw [← map_natCast (algebraMap K B), CharP.cast_eq_zero, map_zero]

end TauCeti
