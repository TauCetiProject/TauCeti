/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Canonical
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Killing.EndSubalgebra
import TauCeti.LinearAlgebra.End.Adjoin

/-!
# The internal Jordan decomposition in faithful representations

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over an algebraically
closed field `K` of characteristic zero, and let `ρ : L → 𝔤𝔩(V)` be a faithful finite-dimensional
representation. The internal Jordan decomposition `x = xₙ + xₛ` of `x : L`
(`TauCeti.LieAlgebra.nilpotentPart`, `TauCeti.LieAlgebra.semisimplePart`) is defined through the
adjoint endomorphism `ad x`, whereas `ρ x` has its own Jordan–Chevalley decomposition in
`Module.End K V`. This file proves that the two agree: `ρ xₙ` is the nilpotent part and `ρ xₛ`
the semisimple part of `ρ x`. In particular the internal decomposition can be computed in any
faithful representation, and an element is ad-semisimple exactly when its image is semisimple.

The heart of the matter is a statement about Lie subalgebras of `𝔤𝔩(V)`: **a Lie subalgebra
`L ⊆ 𝔤𝔩(V)` with nondegenerate Killing form contains the semisimple and nilpotent parts of each of
its elements** (`LieSubalgebra.mem_of_isNilpotent_of_add_mem`,
`LieSubalgebra.mem_of_isSemisimple_of_add_mem`). Write `x = n + s` for the Jordan–Chevalley
decomposition of `x ∈ L`. Then:

* `ad n` is a polynomial in `ad x`, so `ad n` preserves `L`;
* `n` is a polynomial in `x`, so `n` preserves every `L`-submodule `W ⊆ V`, and its restriction to
  `W` is nilpotent, hence has trace zero.

Hence `n ∈ L` by the membership criterion `LieSubalgebra.mem_of_forall_lie_mem` for Killing Lie
subalgebras of `𝔤𝔩(V)`, whose proof combines Weyl's theorem, Schur's lemma and the vanishing of
traces on a perfect Lie algebra.

For a faithful representation `ρ`, its image is isomorphic to `L`, so it is a Killing Lie
subalgebra of `𝔤𝔩(V)`; the parts of `ρ x` lie in it and form the internal Jordan decomposition
there, which is the image of the internal Jordan decomposition of `x`
(`LieEquiv.map_jordanDecomposition`). That ad-nilpotent elements act nilpotently holds in an
arbitrary finite-dimensional representation (`TauCeti.isNilpotent_apply_of_isNilpotent_ad`), and
the converse for faithful representations (`LieHom.isNilpotent_apply_iff_isNilpotent_ad`) lives
beside it in `TauCeti.RepresentationTheory.Lie.AdNilpotent`; this file does not treat semisimple
parts in representations with a nonzero kernel.

## Main results

* `LieSubalgebra.mem_of_isNilpotent_of_add_mem`, `LieSubalgebra.mem_of_isSemisimple_of_add_mem`:
  a Killing Lie subalgebra of `𝔤𝔩(V)` contains the Jordan–Chevalley parts of its elements.
* `LieHom.apply_nilpotentPart_eq`, `LieHom.apply_semisimplePart_eq`: a faithful representation
  carries the internal Jordan decomposition of `x` to the Jordan–Chevalley decomposition of `ρ x`.
* `LieHom.isSemisimple_apply_semisimplePart`: under a faithful representation the image of the
  semisimple part is semisimple.
* `LieHom.isSemisimple_apply_iff_isSemisimple_ad`: under a faithful representation,
  ad-semisimplicity is detected by the image.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.4
  (Theorem and Corollary).
-/

public section

open LieAlgebra LieModule Module Module.End

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [CharZero K] [IsAlgClosed K] (L : LieSubalgebra K (Module.End K V)) [IsKilling K L]

/-- **A Killing Lie subalgebra of `𝔤𝔩(V)` contains the nilpotent parts of its elements.** Over an
algebraically closed field of characteristic zero, if `L ⊆ 𝔤𝔩(V)` has nondegenerate Killing form
and `n + s ∈ L` is a Jordan–Chevalley decomposition (`n` nilpotent, `s` semisimple, commuting),
then `n ∈ L`. -/
theorem mem_of_isNilpotent_of_add_mem {n s : Module.End K V} (hc : Commute n s)
    (hn : IsNilpotent n) (hs : s.IsSemisimple) (hx : n + s ∈ L) : n ∈ L := by
  -- `n` is a polynomial in `n + s`, by uniqueness of the Jordan–Chevalley decomposition.
  have hnx : n ∈ Algebra.adjoin K {n + s} := by
    obtain ⟨n', hn', s', hs', hn'nil, hs'ss, hns'⟩ := (n + s).exists_isNilpotent_isSemisimple
    have hc' : Commute n' s' := Algebra.commute_of_mem_adjoin_singleton_of_commute hs'
      (Algebra.commute_of_mem_adjoin_self hn').symm
    rwa [(isNilpotent_isSemisimple_unique hn'nil hs'ss hn hs hc' hc hns'.symm).1] at hn'
  -- So `n` preserves every `L`-submodule of `V`, with nilpotent restriction.
  have hWn (W : LieSubmodule K L V) : ∀ w ∈ W, n w ∈ W := by
    refine (mem_invtSubmodule_iff_forall_mem_of_mem n).1 <|
      TauCeti.mem_invtSubmodule_of_mem_adjoin (s := {n + s}) ?_ hnx
    rintro _ rfl
    exact (mem_invtSubmodule_iff_forall_mem_of_mem _).2 (apply_mem_of_mem L hx W)
  refine mem_of_forall_lie_mem L n (fun z hz ↦ ?_) hWn fun W ↦
    (LinearMap.isNilpotent_trace_of_isNilpotent (isNilpotent.restrict _ hn)).eq_zero
  -- `ad n` is a polynomial in `ad (n + s)`, which preserves `L`, so `ad n` preserves `L`.
  refine (mem_invtSubmodule_iff_forall_mem_of_mem (ad K _ n) (p := L.toSubmodule)).1 ?_ z hz
  refine TauCeti.mem_invtSubmodule_of_mem_adjoin (s := {ad K _ (n + s)}) ?_
    (ad_mem_adjoin_of_isNilpotent hc hn hs)
  rintro _ rfl
  exact (mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun z hz ↦ L.lie_mem hx hz

/-- **A Killing Lie subalgebra of `𝔤𝔩(V)` contains the semisimple parts of its elements.** Over an
algebraically closed field of characteristic zero, if `L ⊆ 𝔤𝔩(V)` has nondegenerate Killing form
and `n + s ∈ L` is a Jordan–Chevalley decomposition (`n` nilpotent, `s` semisimple, commuting),
then `s ∈ L`. -/
theorem mem_of_isSemisimple_of_add_mem {n s : Module.End K V} (hc : Commute n s)
    (hn : IsNilpotent n) (hs : s.IsSemisimple) (hx : n + s ∈ L) : s ∈ L := by
  simpa using L.sub_mem hx (L.mem_of_isNilpotent_of_add_mem hc hn hs hx)

end LieSubalgebra

namespace LieHom

open TauCeti.LieAlgebra

variable {K L V : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [IsAlgClosed K]

/-- **A faithful representation carries the internal semisimple part to the Jordan–Chevalley
semisimple part.** If `ρ` is injective and `ρ x = n + s` is a Jordan–Chevalley decomposition, then
`ρ` maps the semisimple part of `x` to `s`. -/
theorem apply_semisimplePart_eq (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
    {x : L} {n s : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hx : ρ x = n + s) : ρ (semisimplePart K x) = s := by
  let e := LieEquiv.ofInjective ρ hρ
  have : IsKilling K ρ.range := e.isKilling
  have hmem : n + s ∈ ρ.range := hx ▸ ρ.mem_range_self x
  have hn' := ρ.range.mem_of_isNilpotent_of_add_mem hc hn hs hmem
  have hs' := ρ.range.mem_of_isSemisimple_of_add_mem hc hn hs hmem
  -- Inside the image, `(n, s)` is the internal Jordan decomposition of `e x = ρ x`.
  have key : ((⟨n, hn'⟩ : ρ.range), (⟨s, hs'⟩ : ρ.range)) = jordanDecomposition K (e x) := by
    refine (eq_jordanDecomposition_iff K _ _ _).2 ⟨?_, ?_, ?_, ?_⟩
    · exact isNilpotent_ad_of_isNilpotent hn
    · exact ρ.range.isSemisimple_ad_of_isSemisimple_ad (ad_isSemisimple_of_isSemisimple hs)
    · exact Subtype.ext (by simp [LieRing.of_associative_ring_bracket, hc.eq])
    · exact Subtype.ext (by simp [e, hx])
  have h := congrArg (fun y ↦ (y.2 : Module.End K V)) key
  simpa [e, ← semisimplePart_def] using h.symm

/-- **A faithful representation carries the internal nilpotent part to the Jordan–Chevalley
nilpotent part.** If `ρ` is injective and `ρ x = n + s` is a Jordan–Chevalley decomposition, then
`ρ` maps the nilpotent part of `x` to `n`. -/
theorem apply_nilpotentPart_eq (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
    {x : L} {n s : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hx : ρ x = n + s) : ρ (nilpotentPart K x) = n := by
  have h := congrArg ρ (nilpotentPart_add_semisimplePart K x)
  rw [map_add, ρ.apply_semisimplePart_eq hρ hc hn hs hx, hx] at h
  exact add_right_cancel h

/-- A faithful finite-dimensional representation of a Killing Lie algebra over an algebraically
closed field of characteristic zero carries the semisimple part of the internal Jordan
decomposition to a semisimple endomorphism. -/
@[simp]
theorem isSemisimple_apply_semisimplePart (ρ : L →ₗ⁅K⁆ Module.End K V)
    (hρ : Function.Injective ρ) (x : L) : (ρ (semisimplePart K x)).IsSemisimple := by
  obtain ⟨n, hn, s, hs, hn_nil, hs_ss, hx⟩ := (ρ x).exists_isNilpotent_isSemisimple
  have hc : Commute n s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs
    (Algebra.commute_of_mem_adjoin_self hn).symm
  rw [ρ.apply_semisimplePart_eq hρ hc hn_nil hs_ss hx]
  exact hs_ss

/-- Under a faithful finite-dimensional representation, an element of a Killing Lie algebra over an
algebraically closed field of characteristic zero is ad-semisimple exactly when its image is
semisimple. -/
theorem isSemisimple_apply_iff_isSemisimple_ad (ρ : L →ₗ⁅K⁆ Module.End K V)
    (hρ : Function.Injective ρ) (x : L) :
    (ρ x).IsSemisimple ↔ (ad K L x).IsSemisimple := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa [h] using ρ.isSemisimple_apply_semisimplePart hρ x⟩
  rw [← nilpotentPart_eq_zero_iff K, ← hρ.eq_iff, map_zero]
  exact ρ.apply_nilpotentPart_eq hρ (Commute.zero_left _) IsNilpotent.zero h (zero_add _).symm

end LieHom
