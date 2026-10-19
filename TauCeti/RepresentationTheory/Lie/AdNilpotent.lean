/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Eigenvector
public import TauCeti.Algebra.Lie.Derivation.Solvable
public import TauCeti.Algebra.Lie.Killing.AdNilpotent
public import TauCeti.Algebra.Lie.SemiDirect.AdNilpotent
public import TauCeti.Algebra.Lie.Solvable.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Ad-nilpotent elements in finite-dimensional representations

Over a field of characteristic zero, an ad-nilpotent element of a finite-dimensional Lie
algebra with nondegenerate Killing form acts nilpotently in every finite-dimensional
representation. This is the semisimple part of the nilpotence-preservation argument in
Hochschild's strengthening of Ado's theorem.

The Killing form supplies `t` with `⁅x, t⁆ = x`. Applying a representation gives a nonzero
commutator eigenvalue for the operator representing `x`. This operator is algebraic because
the representation is finite dimensional, so the associative derivation result proves it
nilpotent. Neither algebraic closedness nor a choice of `sl₂`-triple is needed.

For a Killing Lie subalgebra `S` of a finite-dimensional `L`, apply the result to the restricted
adjoint action on `L` and the restricted action on a finite-dimensional `L`-module `M`.
Nilpotence of `ad_S s` implies nilpotence of `ad_L s` and of the action of `s` on `M`. These
applications use the subalgebra and its Killing form, without requiring a decomposition of `L`.

For an arbitrary finite-dimensional `L` in characteristic zero, the same conclusion holds on every
finite-dimensional `L`-module on which the nilradical acts nilpotently. Given a Levi complement
`S`, a Lie subalgebra complementary to the solvable radical `R`, write an `ad`-nilpotent `x` as
`r + s` with `r ∈ R` and `s ∈ S`. The component `s` is `ad`-nilpotent in `S`, and `S ≅ L ⧸ R` is
Killing, so `s` acts nilpotently on `L` and on the module. The nilpotent-extension lemma, applied
on `L` to the span of `s` and the nilradical `N` and then to its extension by `x`, which normalizes
it because `⁅L, R⁆ ≤ N`, shows that `r = x - s` is `ad`-nilpotent; the radical criterion gives
`r ∈ N`. On the module, `s` and `N` act nilpotently, hence so does `x = s + r`.

## Main results

* `TauCeti.isNilpotent_apply_of_lie_eq_smul`: a nonzero adjoint eigenvalue forces nilpotence
  in every finite-dimensional representation.
* `TauCeti.isNilpotent_toEnd_of_isNilpotent_ad`: ad-nilpotence in a finite-dimensional Killing
  Lie algebra implies nilpotence in every finite-dimensional Lie module.
* `TauCeti.isNilpotent_apply_of_isNilpotent_ad`: the same result for an explicit Lie
  homomorphism into an endomorphism algebra.
* `LieSubalgebra.isNilpotent_toEnd_of_isNilpotent_ad_of_isCompl_radical`: in characteristic
  zero, an `ad`-nilpotent element acts nilpotently on every finite-dimensional module on which the
  nilradical acts nilpotently.
* `LieSubalgebra.isNilpotent_apply_of_isNilpotent_ad_of_isCompl_radical`: the same result for an
  explicit Lie homomorphism into an endomorphism algebra.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531–533.
-/

public section

open LieAlgebra LieModule

namespace TauCeti

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

-- Endomorphism algebras carry the associative commutator bracket locally.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- An element with nonzero eigenvalue for an adjoint action has nilpotent image in every
finite-dimensional representation in characteristic zero. The Lie algebra need not be
finite dimensional or semisimple. -/
theorem isNilpotent_apply_of_lie_eq_smul {ρ : L →ₗ⁅K⁆ Module.End K M}
    {x y : L} {c : K} (hc : c ≠ 0) (hxy : ⁅y, x⁆ = c • x) : IsNilpotent (ρ x) := by
  apply derivationLieAlgebra.isNilpotent_of_isAlgebraic_of_apply_eq_smul
    (innerDerivation K (ρ y)) (IsAlgebraic.of_finite K _) hc
  rw [coe_innerDerivation, ad_apply, ← LieHom.map_lie, hxy, map_smul]

/-- An ad-nilpotent element has nilpotent image under every finite-dimensional representation
of a Killing Lie algebra over a characteristic-zero field. -/
theorem isNilpotent_apply_of_isNilpotent_ad [FiniteDimensional K L] [IsKilling K L]
    {ρ : L →ₗ⁅K⁆ Module.End K M} {x : L} (hx : IsNilpotent (ad K L x)) :
    IsNilpotent (ρ x) := by
  obtain ⟨t, ht⟩ := exists_lie_eq_self_of_isNilpotent_ad hx
  apply isNilpotent_apply_of_lie_eq_smul (y := t) (c := -1) (by simp)
  simpa [ht] using (lie_skew t x).symm

/-- An ad-nilpotent element of a finite-dimensional Killing Lie algebra acts nilpotently in
every finite-dimensional Lie module over a characteristic-zero field. -/
theorem isNilpotent_toEnd_of_isNilpotent_ad [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K L] [IsKilling K L] {x : L} (hx : IsNilpotent (ad K L x)) :
    IsNilpotent (toEnd K L M x) :=
  isNilpotent_apply_of_isNilpotent_ad hx

end TauCeti

namespace LieSubalgebra

open TauCeti

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

-- Endomorphism algebras carry the associative commutator bracket locally.
attribute [local instance 100] LieRing.ofAssociativeRing

section Radical

variable [LieRingModule L M] [LieModule K L M] [FiniteDimensional K L]

/-- **Hochschild's nilpotence theorem** in characteristic zero: if the nilradical of a
finite-dimensional Lie algebra `L` acts nilpotently on a finite-dimensional `L`-module `M`, then
so does every `ad`-nilpotent element of `L`. The Lie subalgebra `S` is any Levi complement, that
is, any complement of the solvable radical; the conclusion does not depend on it. -/
theorem isNilpotent_toEnd_of_isNilpotent_ad_of_isCompl_radical (S : LieSubalgebra K L)
    (hS : IsCompl (radical K L).toSubmodule S.toSubmodule)
    (hM : ∀ n ∈ LieAlgebra.nilradical K L, IsNilpotent (toEnd K L M n)) {x : L}
    (hx : IsNilpotent (ad K L x)) : IsNilpotent (toEnd K L M x) := by
  -- `S` is isomorphic to `L ⧸ radical K L`, which is Killing by Cartan's criterion
  have : IsKilling K S := isKilling_of_equiv ((radical K L).quotientEquivOfIsCompl S hS)
  obtain ⟨r, hr, s, hs, rfl⟩ := Submodule.mem_sup.mp (hS.sup_eq_top ▸ Submodule.mem_top (x := x))
  -- the adjoint action is the action of `L` on itself as a Lie module, by definition
  have had (z : L) : ad K L z = toEnd K L L z := (rfl)
  -- the component `s` is `ad`-nilpotent in `S`, hence acts nilpotently on `L` and on `M`
  have hsS : IsNilpotent (ad K S ⟨s, hs⟩) :=
    (radical K L).isNilpotent_ad_right_of_isCompl S hS ⟨r, hr⟩ ⟨s, hs⟩ hx
  have hsL : IsNilpotent (toEnd K L L s) := by
    simpa only [LieSubalgebra.toEnd_mk] using isNilpotent_toEnd_of_isNilpotent_ad (M := L) hsS
  have hsM : IsNilpotent (toEnd K L M s) := by
    simpa only [LieSubalgebra.toEnd_mk] using isNilpotent_toEnd_of_isNilpotent_ad (M := M) hsS
  -- `H`, spanned by `s` and the nilradical `N`, acts nilpotently on `L`
  set N : LieSubalgebra K L := (LieAlgebra.nilradical K L : LieSubalgebra K L)
  have hsN : s ∈ N.normalizer := by
    rw [LieIdeal.normalizer_eq_top]
    exact LieSubalgebra.mem_top s
  set H := LieSubalgebra.lieSpan K L (insert s (N : Set L))
  have hNH : N ≤ H := fun _ hn => LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ hn)
  have hH (z : L) (hz : z ∈ H) : IsNilpotent (toEnd K L L z) :=
    N.isNilpotent_toEnd_of_mem_lieSpan_insert_of_forall hsN
      (fun n hn => had n ▸ LieAlgebra.isNilpotent_ad_of_mem_nilradical hn) hsL hz
  -- `x = r + s` normalizes `H`, since `⁅r + s, t • s + n⁆ = ⁅r, t • s + n⁆ + ⁅s, n⁆ ∈ N`
  have hxH : r + s ∈ H.normalizer := by
    rw [LieSubalgebra.mem_normalizer_iff]
    intro y hy
    obtain ⟨t, n, hn, rfl⟩ := (N.mem_lieSpan_insert_iff hsN).mp hy
    apply hNH
    rw [add_lie, lie_add s, lie_smul, lie_self, smul_zero, zero_add, ← lie_skew r]
    exact add_mem (neg_mem (LieAlgebra.lie_radical_le_nilradical K L
      (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hr)))
      ((LieAlgebra.nilradical K L).lie_mem hn)
  -- so the radical component `r = 1 • x - s` is `ad`-nilpotent, hence lies in the nilradical
  have hrL : IsNilpotent (ad K L r) := by
    have hr' : r = (1 : K) • (r + s) + -s := by rw [one_smul, add_neg_cancel_right]
    rw [had, hr']
    exact H.isNilpotent_toEnd_of_mem_lieSpan_insert_of_forall hxH hH (had _ ▸ hx)
      (H.smul_add_mem_lieSpan_insert hxH 1 (neg_mem (LieSubalgebra.subset_lieSpan
        (Set.mem_insert s _))))
  have hrN : r ∈ LieAlgebra.nilradical K L :=
    LieAlgebra.mem_nilradical_of_mem_radical_of_isNilpotent_ad hr hrL
  -- on `M`, both `s` and the nilradical act nilpotently, hence so does `r + s`
  simpa only [one_smul, add_comm s r] using
    (LieAlgebra.nilradical K L).isNilpotent_toEnd_smul_add_of_mem hM hsM 1 hrN

end Radical

/-- The form of `isNilpotent_toEnd_of_isNilpotent_ad_of_isCompl_radical` for an explicit Lie
homomorphism into an endomorphism algebra: if every element of the nilradical has nilpotent image,
then so does every `ad`-nilpotent element. -/
theorem isNilpotent_apply_of_isNilpotent_ad_of_isCompl_radical [FiniteDimensional K L]
    (S : LieSubalgebra K L) (hS : IsCompl (radical K L).toSubmodule S.toSubmodule)
    {ρ : L →ₗ⁅K⁆ Module.End K M} (hρ : ∀ n ∈ LieAlgebra.nilradical K L, IsNilpotent (ρ n))
    {x : L} (hx : IsNilpotent (ad K L x)) : IsNilpotent (ρ x) := by
  let := LieRingModule.compLieHom M ρ
  have := LieModule.compLieHom (R := K) M ρ
  have h (z : L) : toEnd K L M z = ρ z := by
    ext m
    simp [LieRingModule.compLieHom_apply]
  rw [← h]
  exact S.isNilpotent_toEnd_of_isNilpotent_ad_of_isCompl_radical hS (fun n hn => h n ▸ hρ n hn) hx

end LieSubalgebra
