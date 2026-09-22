/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SemiDirect
public import TauCeti.Algebra.Lie.Derivation.Quotient
public import TauCeti.Algebra.Lie.OfAssociative
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation

/-!
# The multiplication-plus-derivation representation of a semidirect sum

Let `S` and `H` be Lie algebras over `R`, let `ψ : H →ₗ⁅R⁆ LieDerivation R S S` be an action of
`H` on `S` by derivations, and let `J` be a two-sided ideal of the enveloping algebra `U(S)` that
is stable under the lift `(ψ z)ᵁ` of every derivation in the image of `ψ`. This file makes the
quotient algebra `U(S) ⧸ J` a representation of the semidirect sum `S ⋊⁅ψ⁆ H`:

`(y + z) · a = ι y * a + (ψ z)ᵁ a`.

An element of `S` acts by left multiplication by its canonical generator, and an element of `H`
acts by the derivation of `U(S) ⧸ J` that `(ψ z)ᵁ` descends to. Three commutator identities make
this a Lie homomorphism, one for each pair of summands: two multiplications commute up to the
multiplication by their bracket, two lifted derivations up to the lifted derivation of their
bracket, and -- the identity that produces the twist -- a derivation and a multiplication satisfy

`⁅Dᵁ, ι y · -⁆ = ι (D y) · -`,

which is nothing but the Leibniz rule with the second summand cancelled. Matching this against
the bracket `⁅(y₁, z₁), (y₂, z₂)⁆ = (⁅y₁, y₂⁆ + ψ z₁ y₂ - ψ z₂ y₁, ⁅z₁, z₂⁆)` of the semidirect
sum is exactly what the twist in `LieAlgebra.SemiDirectSum` was designed for.

The construction is the extension step of the Ado--Iwasawa argument: `S` is a solvable ideal of a
Lie algebra `L`, `H` is a complementary subalgebra, and `J` is a derivation-stable cofinite ideal
chosen so that `U(S) ⧸ J` is finite-dimensional. The representation of `S` one starts from is
visible through the ideal alone, which is why the kernel statement below is sharp: an element `y`
of `S` acts by zero exactly when `ι y ∈ J`.

## Main definitions

* `TauCeti.semiDirectEnvelopingRep`: the representation of `S ⋊⁅ψ⁆ H` on `U(S) ⧸ J`.

## Main results

* `TauCeti.semiDirectEnvelopingRep_apply_mk`: the action, on a class of `U(S) ⧸ J`.
* `TauCeti.lie_semiDirectEnvelopingRep_inl_inl`,
  `TauCeti.lie_semiDirectEnvelopingRep_inr_inr` and
  `TauCeti.lie_semiDirectEnvelopingRep_inr_inl`: the three commutator identities, one for each
  pair of summands.
* `TauCeti.semiDirectEnvelopingRep_comp_inl`: the construction extends the left-regular
  representation of `S` on `U(S) ⧸ J`.
* `TauCeti.inl_mem_ker_semiDirectEnvelopingRep_iff`: **kernel control**, `y : S` acts by zero
  exactly when `ι y ∈ J`.
* `TauCeti.apply_eq_zero_of_inl_mem_ker_semiDirectEnvelopingRep`: if `J` is contained in the
  kernel of the enveloping extension of a representation `σ` of `S`, then every `y : S` killed by
  the construction is already killed by `σ`.

## Implementation notes

The split hypothesis on the ambient Lie algebra is stated externally, through Mathlib's
`LieAlgebra.SemiDirectSum`, so that no vector-space complement is chosen here. Stability of `J` is
phrased as membership in `TauCeti.stableDerivations`, the form in which
`TauCeti.derivationQuotientHom` consumes it;
`TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_range_le_iff` reduces the stronger
range condition to a condition on `S` alone. For the adjoint action `ψ = LieDerivation.ad` the
hypothesis holds for every two-sided ideal, by
`TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ad_mem_stableDerivations`.

The two halves of the action are `private`: as terms they are `TauCeti.LieHom.leftRegularRep` and
`TauCeti.derivationQuotientHom` applied to data already in the library, so naming them publicly
would add a layer without adding content. The characterisations on a class `Ideal.Quotient.mk J a`
are the public interface. Only the general one, `TauCeti.semiDirectEnvelopingRep_apply_mk`, is a
`simp` lemma: with it in the default set `simp` already reduces the two summand-wise
specialisations and the kernel criterion, so tagging those as well is what the `simpNF` linter
rejects.

Nilpotence of the constructed operators is *not* proved here: it needs hypotheses relating the
nilradicals of `S` and of the ambient algebra.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, Proposition E.5.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable (R : Type u) (S : Type v) {H : Type w}
variable [CommRing R] [LieRing S] [LieAlgebra R S] [LieRing H] [LieAlgebra R H]

local notation "U" => _root_.UniversalEnvelopingAlgebra R S

variable (ψ : H →ₗ⁅R⁆ LieDerivation R S S)
variable (J : Ideal (_root_.UniversalEnvelopingAlgebra R S)) [J.IsTwoSided]

/-! ### The two summands of the action -/

-- The `S`-half of the action: left multiplication by the class of the canonical generator.  It is
-- a construction internal to `TauCeti.semiDirectEnvelopingRep`, whose `_apply_mk` lemmas are the
-- public interface.
private def envelopingQuotientMul : S →ₗ⁅R⁆ Module.End R (U ⧸ J) :=
  LieHom.leftRegularRep
    ((Ideal.Quotient.mkₐ R J).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι R))

private theorem envelopingQuotientMul_apply_mk (y : S) (a : U) :
    envelopingQuotientMul R S J y (Ideal.Quotient.mk J a)
      = Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R y * a) := by
  rw [envelopingQuotientMul, LieHom.leftRegularRep_apply, LieHom.comp_apply,
    AlgHom.toLieHom_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_mul]

section Construction

variable (hψ : ∀ z : H,
  UniversalEnvelopingAlgebra.envelopingDerivation R S (ψ z) ∈
    stableDerivations R (J.restrictScalars R))

include hψ

-- The lifted derivations, corestricted to the stable ones.  The pattern is
-- `TauCeti.stableInnerDerivation`: a `codRestrict` of the underlying linear map, with the bracket
-- law inherited from the uncorestricted homomorphism.
omit [J.IsTwoSided] in
private theorem comp_envelopingDerivationHom_mem (z : H) :
    ((UniversalEnvelopingAlgebra.envelopingDerivationHom R S).comp ψ) z ∈
      (stableDerivations R (J.restrictScalars R)).toSubmodule := by
  simpa using hψ z

private noncomputable def envelopingQuotientStable :
    H →ₗ⁅R⁆ stableDerivations R (J.restrictScalars R) :=
  { ((UniversalEnvelopingAlgebra.envelopingDerivationHom R S).comp ψ).toLinearMap.codRestrict
      (stableDerivations R (J.restrictScalars R)).toSubmodule
      (comp_envelopingDerivationHom_mem R S ψ J hψ) with
    map_lie' := fun {z w} => Subtype.ext
      (((UniversalEnvelopingAlgebra.envelopingDerivationHom R S).comp ψ).map_lie z w) }

-- The `H`-half of the action: the descended derivation of `U(S) ⧸ J`.
private noncomputable def envelopingQuotientDer : H →ₗ⁅R⁆ Module.End R (U ⧸ J) :=
  (derivationLieAlgebra R (U ⧸ J)).incl.comp
    ((derivationQuotientHom R J).comp (envelopingQuotientStable R S ψ J hψ))

omit [J.IsTwoSided] in
private theorem coe_envelopingQuotientStable (z : H) :
    ((envelopingQuotientStable R S ψ J hψ z : stableDerivations R (J.restrictScalars R)) :
        derivationLieAlgebra R (_root_.UniversalEnvelopingAlgebra R S))
      = UniversalEnvelopingAlgebra.envelopingDerivation R S (ψ z) := by
  have h : ((envelopingQuotientStable R S ψ J hψ z :
        stableDerivations R (J.restrictScalars R)) :
        derivationLieAlgebra R (_root_.UniversalEnvelopingAlgebra R S))
      = ((UniversalEnvelopingAlgebra.envelopingDerivationHom R S).comp ψ) z := rfl
  rw [h, LieHom.comp_apply, UniversalEnvelopingAlgebra.envelopingDerivationHom_apply]

-- `TauCeti.envelopingQuotientDer` is `TauCeti.derivationQuotientHom` composed with the inclusion
-- of the derivation subalgebra, so its value is the underlying endomorphism of the descended
-- derivation.  Composing with `LieSubalgebra.incl` is the coercion on the nose, and this lemma is
-- the single place that is used; everything below rewrites with it.
private theorem envelopingQuotientDer_apply (z : H) :
    envelopingQuotientDer R S ψ J hψ z
      = (derivationQuotientHom R J (envelopingQuotientStable R S ψ J hψ z) :
          Module.End R (_root_.UniversalEnvelopingAlgebra R S ⧸ J)) :=
  (rfl)

private theorem envelopingQuotientDer_apply_mk (z : H) (a : U) :
    envelopingQuotientDer R S ψ J hψ z (Ideal.Quotient.mk J a)
      = Ideal.Quotient.mk J
        ((UniversalEnvelopingAlgebra.envelopingDerivation R S (ψ z) : Module.End R U) a) := by
  rw [envelopingQuotientDer_apply, derivationQuotientHom_apply_mk, coe_envelopingQuotientStable]

/-- **The mixed commutator identity.** Bracketing the descended derivation attached to `z : H`
with multiplication by `y : S` is multiplication by `ψ z y`: the Leibniz rule produces two
summands, and the second is exactly the composite in the other order. -/
private theorem lie_envelopingQuotientDer_envelopingQuotientMul (z : H) (y : S) :
    ⁅envelopingQuotientDer R S ψ J hψ z, envelopingQuotientMul R S J y⁆
      = envelopingQuotientMul R S J (ψ z y) := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    envelopingQuotientMul_apply_mk, envelopingQuotientDer_apply_mk,
    envelopingQuotientDer_apply_mk, envelopingQuotientMul_apply_mk,
    envelopingQuotientMul_apply_mk,
    UniversalEnvelopingAlgebra.envelopingDerivation_mul,
    UniversalEnvelopingAlgebra.envelopingDerivation_ι, map_add, add_sub_cancel_right]

/-! ### The representation -/

/-- **The multiplication-plus-derivation representation.** The semidirect sum `S ⋊⁅ψ⁆ H` acts on
`U(S) ⧸ J` by letting `y : S` multiply on the left by the class of `ι y`, and `z : H` act by the
descended lift of the derivation `ψ z`. -/
noncomputable def semiDirectEnvelopingRep : (S ⋊⁅ψ⁆ H) →ₗ⁅R⁆ Module.End R (U ⧸ J) where
  toFun x := envelopingQuotientMul R S J x.left + envelopingQuotientDer R S ψ J hψ x.right
  map_add' x y := by
    simp only [LieAlgebra.SemiDirectSum.add_eq_mk, map_add]
    abel
  map_smul' t x := by
    simp only [LieAlgebra.SemiDirectSum.smul_eq_mk, map_smul, RingHom.id_apply, smul_add]
  map_lie' {x y} := by
    simp only [LieAlgebra.SemiDirectSum.lie_eq_mk]
    rw [add_lie, lie_add, lie_add, map_sub, map_add,
      (envelopingQuotientMul R S J).map_lie, (envelopingQuotientDer R S ψ J hψ).map_lie,
      lie_envelopingQuotientDer_envelopingQuotientMul,
      ← lie_skew (envelopingQuotientMul R S J x.left) (envelopingQuotientDer R S ψ J hψ y.right),
      lie_envelopingQuotientDer_envelopingQuotientMul]
    abel

-- The defining description of the action.  `TauCeti.semiDirectEnvelopingRep` is built from its
-- `toFun`, so this is the one lemma that has to see through the structure; the public
-- characterisations below are rewritten from it.
private theorem semiDirectEnvelopingRep_apply (x : S ⋊⁅ψ⁆ H) :
    semiDirectEnvelopingRep R S ψ J hψ x
      = envelopingQuotientMul R S J x.left + envelopingQuotientDer R S ψ J hψ x.right :=
  (rfl)

private theorem semiDirectEnvelopingRep_inl (y : S) :
    semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ y)
      = envelopingQuotientMul R S J y := by
  simp only [semiDirectEnvelopingRep_apply, LieAlgebra.SemiDirectSum.inl_eq_mk, map_zero, add_zero]

private theorem semiDirectEnvelopingRep_inr (z : H) :
    semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ z)
      = envelopingQuotientDer R S ψ J hψ z := by
  simp only [semiDirectEnvelopingRep_apply, LieAlgebra.SemiDirectSum.inr_eq_mk, map_zero, zero_add]

/-- The action of a general element of the semidirect sum on a class of `U(S) ⧸ J`. -/
@[simp]
theorem semiDirectEnvelopingRep_apply_mk (x : S ⋊⁅ψ⁆ H) (a : U) :
    semiDirectEnvelopingRep R S ψ J hψ x (Ideal.Quotient.mk J a)
      = Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R x.left * a
          + (UniversalEnvelopingAlgebra.envelopingDerivation R S (ψ x.right) :
              Module.End R U) a) := by
  rw [semiDirectEnvelopingRep_apply, LinearMap.add_apply, envelopingQuotientMul_apply_mk,
    envelopingQuotientDer_apply_mk, map_add]

/-- On the ideal summand the representation is left multiplication by the canonical generator. -/
theorem semiDirectEnvelopingRep_inl_apply_mk (y : S) (a : U) :
    semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ y)
        (Ideal.Quotient.mk J a)
      = Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R y * a) := by
  rw [semiDirectEnvelopingRep_inl, envelopingQuotientMul_apply_mk]

/-- On the complementary summand the representation is the descended lifted derivation. -/
theorem semiDirectEnvelopingRep_inr_apply_mk (z : H) (a : U) :
    semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ z)
        (Ideal.Quotient.mk J a)
      = Ideal.Quotient.mk J
        ((UniversalEnvelopingAlgebra.envelopingDerivation R S (ψ z) : Module.End R U) a) := by
  rw [semiDirectEnvelopingRep_inr, envelopingQuotientDer_apply_mk]

/-! ### The commutator identities -/

/-- **Two multiplication operators.** The ideal summand acts by a Lie homomorphism, so the
bracket of two multiplications is the multiplication by the bracket. -/
theorem lie_semiDirectEnvelopingRep_inl_inl (y₁ y₂ : S) :
    ⁅semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ y₁),
        semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ y₂)⁆
      = semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ ⁅y₁, y₂⁆) := by
  rw [← LieHom.map_lie, ← LieHom.map_lie]

/-- **Two lifted derivations.** Descending the lift of a Lie derivation is a homomorphism of Lie
algebras at each of its two stages, so the bracket of two lifted derivations is the lift attached
to the bracket. -/
theorem lie_semiDirectEnvelopingRep_inr_inr (z₁ z₂ : H) :
    ⁅semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ z₁),
        semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ z₂)⁆
      = semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ ⁅z₁, z₂⁆) := by
  rw [← LieHom.map_lie, ← LieHom.map_lie]

/-- **A lifted derivation against a multiplication.** This is the identity that produces the
twist: differentiating a product and cancelling the summand in which the multiplier is untouched
leaves multiplication by the derivative of the multiplier. -/
theorem lie_semiDirectEnvelopingRep_inr_inl (z : H) (y : S) :
    ⁅semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ z),
        semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ y)⁆
      = semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inl ψ (ψ z y)) := by
  have h : ⁅LieAlgebra.SemiDirectSum.inr ψ z, LieAlgebra.SemiDirectSum.inl ψ y⁆
      = LieAlgebra.SemiDirectSum.inl ψ (ψ z y) := by
    ext <;> simp
  rw [← LieHom.map_lie, h]

/-- The complementary summand acts by **derivations** of the quotient algebra, where the ideal
summand acts by **multiplications**; this is the shape of the construction, and it is what the
three commutator identities above are computing. -/
theorem semiDirectEnvelopingRep_inr_mem_derivationLieAlgebra (z : H) :
    semiDirectEnvelopingRep R S ψ J hψ (LieAlgebra.SemiDirectSum.inr ψ z)
      ∈ derivationLieAlgebra R (U ⧸ J) := by
  rw [semiDirectEnvelopingRep_inr, envelopingQuotientDer_apply]
  exact SetLike.coe_mem _

/-- **The construction extends the left-regular representation of the ideal.** Restricted along
the canonical inclusion of `S`, the representation is left multiplication by the image of the
canonical generator. -/
theorem semiDirectEnvelopingRep_comp_inl :
    (semiDirectEnvelopingRep R S ψ J hψ).comp (LieAlgebra.SemiDirectSum.inl ψ)
      = LieHom.leftRegularRep
          ((Ideal.Quotient.mkₐ R J).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι R)) := by
  refine LieHom.ext fun y => LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [LieHom.comp_apply, semiDirectEnvelopingRep_inl_apply_mk, LieHom.leftRegularRep_apply,
    LieHom.comp_apply, AlgHom.toLieHom_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_mul]

/-! ### Kernel control -/

/-- **Kernel control.** An element of the ideal summand acts by zero exactly when its canonical
generator already lies in `J`: the action is faithful on `S` to precisely the extent that `J`
avoids `ι(S)`. -/
theorem inl_mem_ker_semiDirectEnvelopingRep_iff (y : S) :
    LieAlgebra.SemiDirectSum.inl ψ y ∈ (semiDirectEnvelopingRep R S ψ J hψ).ker
      ↔ _root_.UniversalEnvelopingAlgebra.ι R y ∈ J := by
  rw [LieHom.mem_ker]
  constructor
  · intro h
    have := congrArg (fun f : Module.End R (U ⧸ J) => f 1) h
    simp only [LinearMap.zero_apply] at this
    rw [← map_one (Ideal.Quotient.mk J), semiDirectEnvelopingRep_inl_apply_mk, mul_one] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).mp this
  · intro h
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [semiDirectEnvelopingRep_inl_apply_mk, LinearMap.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right a h

/-- **The invariant that lets the extension be iterated.** If `J` is contained in the kernel of
the enveloping extension of a representation `σ` of `S`, then every element of `S` killed by the
extended representation is already killed by `σ`. -/
theorem apply_eq_zero_of_inl_mem_ker_semiDirectEnvelopingRep {A : Type*} [Ring A] [Algebra R A]
    (σ : S →ₗ⁅R⁆ A) (hJ : J ≤ RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R σ))
    {y : S} (hy : LieAlgebra.SemiDirectSum.inl ψ y ∈ (semiDirectEnvelopingRep R S ψ J hψ).ker) :
    σ y = 0 := by
  have h := hJ ((inl_mem_ker_semiDirectEnvelopingRep_iff R S ψ J hψ y).mp hy)
  rwa [RingHom.mem_ker, _root_.UniversalEnvelopingAlgebra.lift_ι_apply] at h

end Construction

end TauCeti
