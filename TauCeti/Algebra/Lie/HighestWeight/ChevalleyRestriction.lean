/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import TauCeti.Algebra.Lie.HighestWeight.TracePower
public import TauCeti.Algebra.Lie.Killing.ChevalleyRestriction
public import TauCeti.Algebra.Lie.Sl2.Weyl.Cartan
import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.OrbitSeparation
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Chevalley's restriction theorem

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero whose Killing
form is nondegenerate, and `H` a splitting Cartan subalgebra. Restricting polynomial functions from
`L` to `H` is, through the Killing identifications, the algebra map
`TauCeti.lieCartanRestriction H : S(L) →ₐ[K] S(H)`. **Chevalley's restriction theorem** says that
it restricts to an isomorphism from the invariants `S(L)^L` onto the Weyl invariants `S(H)^W`
(`TauCeti.linearInvariants H`). It has three parts.

* **Weyl invariance.** The restriction of an invariant is fixed by the coreflection of every root
  (`TauCeti.map_coreflection_lieCartanRestriction`), and the coreflections generate the Weyl
  group.
* **Injectivity** on `S(L)^L` is `LieSubalgebra.lieCartanRestriction_injOn_lieInvariants`: it rests
  on the density of the conjugates of `H` under the inner automorphisms.
* **Surjectivity.** The Weyl invariants form a graded subalgebra, and in each degree `m` they are
  spanned by the power sums `∑_μ dim L(λ)_μ · t_μ ^ m` of the weights of the irreducible modules
  `L(λ)`, `λ` dominant integral
  (`TauCeti.span_highestWeightTracePowerRestriction_eq_linearInvariants_inf_homogeneousSubmodule`).
  Each such power sum is the restriction of the invariant polynomial function
  `x ↦ tr (ρ_λ(x) ^ m)` on `L`. This part uses that `K` is algebraically closed.

Combining surjectivity with finite-group orbit separation on `S(H)^W` shows that two elements of
`H` agree on `S(L*)^L` if and only if they lie in the same Weyl-group orbit
(`TauCeti.forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup`), and in particular at most
one element of `H` where every simple root of a base `b` takes a natural value realizes a given
invariant character (`RootPairing.Base.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant`).
Since invariant polynomial functions are constant on orbits of the group `Int(L)` of inner
automorphisms (`TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`), and the Weyl group
acts on `H` by inner automorphisms
(`TauCeti.exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv`), two elements of `H` are
`Int(L)`-conjugate exactly when they are Weyl-conjugate
(`TauCeti.exists_mem_intLieAlgebra_smul_eq_iff_exists_coweightEquiv_eq`).

## Main definitions

* `LieSubalgebra.lieChevalleyRestrictionIso H`: the isomorphism `S(L)^L ≃ₐ[K] S(H)^W` given by
  restriction to `H`.

## Main results

* `TauCeti.lieCartanRestriction_mem_linearInvariants`: the restriction of an invariant is a Weyl
  invariant.
* `TauCeti.lift_eval_coe_eq_of_coweightEquiv_eq`: Weyl-conjugate elements of `H` agree on
  `S(L*)^L`.
* `LieSubalgebra.linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants`: a homogeneous
  Weyl invariant of degree `m` is the restriction of an invariant of degree `m`.
* `LieSubalgebra.map_lieInvariants_lieCartanRestriction`: the image of `S(L)^L` is `S(H)^W`.
* `LieSubalgebra.lieChevalleyRestrictionIso_mem_homogeneousSubmodule_iff`: the isomorphism
  preserves degrees in both directions.
* `TauCeti.forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup`: two elements of `H` agree
  on `S(L*)^L` if and only if they are conjugate under the Weyl group.
* `TauCeti.exists_coweightEquiv_eq_of_smul_eq`: if `g ∈ Int(L)` carries `x ∈ H` to `y ∈ H`, some
  element of the Weyl group carries `x` to `y`.
* `TauCeti.exists_mem_intLieAlgebra_smul_eq_iff_exists_coweightEquiv_eq`: elements of `H` are
  `Int(L)`-conjugate exactly when they are Weyl-conjugate.
* `RootPairing.Base.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant`: dominant elements of
  `H` agreeing on `S(L*)^L` are equal.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
* J. Dixmier, *Enveloping Algebras*, §7.3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §2.2.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-! ### Weyl invariance -/

section Weyl

variable [IsTriangularizable K H L]

variable {H} in
/-- **The restriction of an invariant is a Weyl invariant**: for `p ∈ S(L)^L`, the restriction
`TauCeti.lieCartanRestriction H p` lies in `S(H)^W`. -/
theorem lieCartanRestriction_mem_linearInvariants {p : _root_.SymmetricAlgebra K L}
    (hp : p ∈ lieInvariants K L L) : lieCartanRestriction H p ∈ linearInvariants H := by
  rw [mem_linearInvariants_iff]
  rintro ⟨w, hw⟩ lam
  induction hw using RootPairing.weylGroup.induction generalizing lam with
  | mem i =>
    -- the reflection of weights is the transpose of the coreflection
    have hs : (⟨_, (rootSystem H).reflection_mem_weylGroup i⟩ : (rootSystem H).weylGroup) • lam =
        lam ∘ₗ ((rootSystem H).coreflection i).toLinearMap :=
      LinearMap.ext fun y ↦ by
        simp [RootPairing.reflection_apply, RootPairing.coreflection_apply, mul_comm]
    rw [hs, ← _root_.SymmetricAlgebra.lift_comp_map, AlgHom.comp_apply,
      map_coreflection_lieCartanRestriction i hp]
  | one => simp
  | mul x y hx hy ihx ihy => rw [← MulMemClass.mk_mul_mk (hx := hx) (hy := hy), mul_smul, ihx, ihy]

variable {H} in
/-- Weyl-conjugate elements of a splitting Cartan subalgebra take equal values at every invariant
polynomial function `p ∈ S(L*)^L`. -/
theorem lift_eval_coe_eq_of_coweightEquiv_eq {h₁ h₂ : H}
    (hw : ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv h₁ = h₂)
    {p : _root_.SymmetricAlgebra K (Dual K L)} (hp : p ∈ lieInvariants K L (Dual K L)) :
    _root_.SymmetricAlgebra.lift (Dual.eval K L (h₁ : L)) p =
      _root_.SymmetricAlgebra.lift (Dual.eval K L (h₂ : L)) p := by
  rw [← (killingSymmetricEquiv K L).apply_symm_apply p] at hp ⊢
  rw [lift_eval_killingSymmetricEquiv_coe, lift_eval_killingSymmetricEquiv_coe]
  exact forall_mem_linearInvariants_lift_cartanEquivDual_eq_iff.mpr hw _
    (lieCartanRestriction_mem_linearInvariants
      ((killingSymmetricEquiv_mem_lieInvariants_iff K L).mp hp))

end Weyl

end TauCeti

namespace LieSubalgebra

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module TauCeti TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-! ### Surjectivity onto the Weyl invariants -/

section Surjective

variable [IsAlgClosed K]

/-- **A homogeneous Weyl invariant is the restriction of a homogeneous invariant.** Every Weyl
invariant `q ∈ S(H)^W` homogeneous of degree `m` is `TauCeti.lieCartanRestriction H p` for some
invariant `p ∈ S(L)^L` homogeneous of degree `m`. -/
theorem linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants (m : ℕ) :
    Subalgebra.toSubmodule (linearInvariants H) ⊓ homogeneousSubmodule K H m ≤
      (Subalgebra.toSubmodule (lieInvariants K L L) ⊓ homogeneousSubmodule K L m).map
        (lieCartanRestriction H).toLinearMap := by
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  rw [← span_highestWeightTracePowerRestriction_eq_linearInvariants_inf_homogeneousSubmodule b m,
    Submodule.span_le]
  rintro _ ⟨lam, hlam, rfl⟩
  have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  -- the power sum of the weights of `L(λ)` is the restriction of `x ↦ tr (ρ_λ(x) ^ m)`
  refine ⟨(killingSymmetricEquiv K L).symm
    (tracePowerPolynomial K L (irreducibleQuotient b lam) m), ⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, ← killingSymmetricEquiv_mem_lieInvariants_iff,
      AlgEquiv.apply_symm_apply]
    exact tracePowerPolynomial_mem_lieInvariants m
  · rw [killingSymmetricEquiv_symm, _root_.SymmetricAlgebra.mapEquiv_apply]
    exact map_mem_homogeneousSubmodule _ (tracePowerPolynomial_mem_homogeneousSubmodule m)
  · rw [AlgHom.toLinearMap_apply,
      lieCartanRestriction_killingSymmetricEquiv_symm_tracePowerPolynomial,
      highestWeightTracePowerRestriction_def]

/-- **Chevalley's restriction theorem, image form.** Restriction to `H` maps the invariants
`S(L)^L` onto the Weyl invariants `S(H)^W`. -/
theorem map_lieInvariants_lieCartanRestriction :
    (lieInvariants K L L).map (lieCartanRestriction H) = linearInvariants H := by
  classical
  refine le_antisymm (Subalgebra.map_le.mpr fun p hp ↦ lieCartanRestriction_mem_linearInvariants hp)
    fun q hq ↦ ?_
  -- the Weyl invariants are graded, so `q` is the sum of its homogeneous Weyl-invariant components
  rw [← DirectSum.sum_support_decompose (homogeneousSubmodule K H) q]
  refine Subalgebra.sum_mem _ fun m _ ↦ ?_
  obtain ⟨p, ⟨hp, -⟩, hpq⟩ := linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants H m
    ⟨isHomogeneous_linearInvariants m hq, SetLike.coe_mem _⟩
  exact ⟨p, hp, hpq⟩

/-- **Chevalley's restriction theorem.** Restriction of polynomial functions from `L` to `H`,
`TauCeti.lieCartanRestriction H`, is an isomorphism from the invariants `S(L)^L` onto the Weyl
invariants `S(H)^W`. -/
noncomputable def lieChevalleyRestrictionIso : lieInvariants K L L ≃ₐ[K] linearInvariants H :=
  AlgEquiv.ofBijective
    (((lieCartanRestriction H).comp (lieInvariants K L L).val).codRestrict (linearInvariants H)
      fun p ↦ lieCartanRestriction_mem_linearInvariants p.property)
    ⟨fun p q hpq ↦ Subtype.ext <| lieCartanRestriction_injOn_lieInvariants H p.property q.property
        (congrArg Subtype.val hpq),
      fun q ↦ by
        obtain ⟨p, hp, hpq⟩ := (map_lieInvariants_lieCartanRestriction H).ge q.property
        exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩⟩

/-- The Chevalley isomorphism is restriction to `H`. -/
@[simp]
theorem coe_lieChevalleyRestrictionIso_apply (p : lieInvariants K L L) :
    (lieChevalleyRestrictionIso H p : _root_.SymmetricAlgebra K H) = lieCartanRestriction H p :=
  (rfl)

/-- The inverse of the Chevalley isomorphism sends a Weyl invariant to the invariant restricting
to it. -/
@[simp]
theorem lieCartanRestriction_lieChevalleyRestrictionIso_symm_apply (q : linearInvariants H) :
    lieCartanRestriction H ((lieChevalleyRestrictionIso H).symm q : _root_.SymmetricAlgebra K L) =
      q := by
  rw [← coe_lieChevalleyRestrictionIso_apply, AlgEquiv.apply_symm_apply]

/-- **The Chevalley isomorphism preserves degrees**: an invariant is homogeneous of degree `m`
exactly when its restriction to `H` is. -/
theorem lieChevalleyRestrictionIso_mem_homogeneousSubmodule_iff {p : lieInvariants K L L}
    {m : ℕ} :
    (lieChevalleyRestrictionIso H p : _root_.SymmetricAlgebra K H) ∈ homogeneousSubmodule K H m ↔
      (p : _root_.SymmetricAlgebra K L) ∈ homogeneousSubmodule K L m := by
  rw [coe_lieChevalleyRestrictionIso_apply]
  refine ⟨fun hq ↦ ?_, lieCartanRestriction_mem_homogeneousSubmodule H⟩
  obtain ⟨p', ⟨hp', hp'm⟩, hpq⟩ := linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants
    H m ⟨lieCartanRestriction_mem_linearInvariants p.property, hq⟩
  rwa [← lieCartanRestriction_injOn_lieInvariants H hp' p.property hpq]

end Surjective

end LieSubalgebra

namespace TauCeti

section CartanSeparation

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module _root_.SymmetricAlgebra
open TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **Invariant polynomials detect Weyl orbits on a Cartan subalgebra.** Over an algebraically
closed field of characteristic zero, two elements `x, y : H` take the same value on every
`L`-invariant polynomial function `p ∈ S(L*)^L` if and only if some element of the Weyl group
carries `x` to `y`. -/
theorem forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup {x y : H} :
    (∀ p ∈ lieInvariants K L (Dual K L),
        lift (Dual.eval K L (x : L)) p = lift (Dual.eval K L (y : L)) p) ↔
      ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y := by
  refine ⟨fun hp ↦ ?_, fun hw p hp ↦ lift_eval_coe_eq_of_coweightEquiv_eq hw hp⟩
  -- Chevalley surjectivity transfers equality on `S(L*)^L` to equality on `S(H)^W`.
  have hlin : ∀ q ∈ linearInvariants H,
      lift (cartanEquivDual H x) q = lift (cartanEquivDual H y) q := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Subalgebra.mem_map.mp
      ((LieSubalgebra.map_lieInvariants_lieCartanRestriction H).ge hq)
    have hr' : killingSymmetricEquiv K L r ∈ lieInvariants K L (Dual K L) :=
      (killingSymmetricEquiv_mem_lieInvariants_iff K L).mpr hr
    rw [← lift_eval_killingSymmetricEquiv_coe, ← lift_eval_killingSymmetricEquiv_coe]
    exact hp _ hr'
  exact forall_mem_linearInvariants_lift_cartanEquivDual_eq_iff.mp hlin

section IntLieAlgebra

variable [LieAlgebra ℚ L]

/-- **Elements of a Cartan subalgebra conjugate under `Int(L)` are Weyl-conjugate.** If an inner
automorphism `g ∈ Int(L)` carries `x ∈ H` to `y ∈ H`, then some element `w` of the Weyl group of
the root system of `H` carries `x` to `y` through its action
`RootPairing.Equiv.coweightEquiv` on `H`. -/
theorem exists_coweightEquiv_eq_of_smul_eq {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {x y : H} (hxy : g • (x : L) = y) :
    ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y :=
  -- invariant polynomial functions are constant on `Int(L)`-orbits
  forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup.mp fun _ hp ↦ by
    rw [← hxy, lift_eval_smul_of_mem_intLieAlgebra hg hp]

/-- **`Int(L)`-conjugacy on a Cartan subalgebra is Weyl conjugacy.** Two elements `x, y` of `H` are
conjugate under the group `Int(L)` of inner automorphisms exactly when some element of the Weyl
group of the root system of `H` carries `x` to `y`. -/
theorem exists_mem_intLieAlgebra_smul_eq_iff_exists_coweightEquiv_eq {x y : H} :
    (∃ g ∈ intLieAlgebra K L, g • (x : L) = y) ↔
      ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y := by
  refine ⟨fun ⟨g, hg, hxy⟩ ↦ exists_coweightEquiv_eq_of_smul_eq hg hxy, fun ⟨w, hw⟩ ↦ ?_⟩
  obtain ⟨g, hg, hgH⟩ := exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv w
  exact ⟨g, hg, by rw [hgH, hw]⟩

end IntLieAlgebra

end CartanSeparation

end TauCeti

namespace RootPairing.Base

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module _root_.SymmetricAlgebra
open TauCeti TauCeti.SymmetricAlgebra

section DominantUniqueness

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **At most one dominant element realizes a given invariant character.** If `x, y : H` both take
natural-number values on every simple root of `b` and agree on every `L`-invariant polynomial
function `p ∈ S(L*)^L`, then `x = y`. -/
theorem eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant (b : (rootSystem H).Base)
    {x y : H} (hx : ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) x = n)
    (hy : ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) y = n)
    (hp : ∀ p ∈ lieInvariants K L (Dual K L),
      lift (Dual.eval K L (x : L)) p = lift (Dual.eval K L (y : L)) p) :
    x = y := by
  obtain ⟨w, rfl⟩ := forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup.mp hp
  exact (b.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply hx hy).symm

end DominantUniqueness

end RootPairing.Base
