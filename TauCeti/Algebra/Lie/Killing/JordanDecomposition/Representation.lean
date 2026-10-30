/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Canonical
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
import Mathlib.Algebra.Lie.TraceForm
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Algebra.Lie.Weights.Central
import TauCeti.LinearAlgebra.End.Adjoin
import TauCeti.RepresentationTheory.Lie.AdNilpotent

/-!
# The internal Jordan decomposition in faithful representations

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over an algebraically
closed field `K` of characteristic zero, and let `ρ : L → 𝔤𝔩(V)` be a faithful finite-dimensional
representation. The internal Jordan decomposition `x = xₙ + xₛ` of `x : L`
(`TauCeti.LieAlgebra.nilpotentPart`, `TauCeti.LieAlgebra.semisimplePart`) is defined through the
adjoint endomorphism `ad x`, whereas `ρ x` has its own Jordan–Chevalley decomposition in
`Module.End K V`. This file proves that the two agree: `ρ xₙ` is the nilpotent part and `ρ xₛ`
the semisimple part of `ρ x`. In particular the internal decomposition can be computed in any
faithful representation, and an element is ad-semisimple (resp. ad-nilpotent) exactly when its
image is semisimple (resp. nilpotent).

The heart of the matter is a statement about Lie subalgebras of `𝔤𝔩(V)`: **a Lie subalgebra
`L ⊆ 𝔤𝔩(V)` with nondegenerate Killing form contains the semisimple and nilpotent parts of each of
its elements** (`LieSubalgebra.mem_of_isNilpotent_of_add_mem`,
`LieSubalgebra.mem_of_isSemisimple_of_add_mem`). Write `x = n + s` for the Jordan–Chevalley
decomposition of `x ∈ L`. Then:

* `ad n` is a polynomial in `ad x`, so `ad n` preserves `L`;
* `n` is a polynomial in `x`, so `n` preserves every `L`-submodule `W ⊆ V`, and its restriction to
  `W` is nilpotent, hence has trace zero.

By Weyl's theorem `L` has an `L`-stable complement `Q` in `𝔤𝔩(V)`; write `n = a + q` with `a ∈ L`
and `q ∈ Q`. The bracket of `q` with `L` lies in `L ∩ Q = 0`, so `q` commutes with `L`. Elements of
`L` have trace zero on each `L`-submodule, because `L` is perfect, so `q` also preserves every
`L`-submodule with trace zero on it. Schur's lemma makes `q` a scalar on each irreducible
`L`-submodule, and that scalar vanishes by the trace condition. Since `V` is a sum of irreducible
submodules, again by Weyl's theorem, `q = 0` and `n = a ∈ L`.

For a faithful representation `ρ`, its image is isomorphic to `L`, so it is a Killing Lie
subalgebra of `𝔤𝔩(V)`; the parts of `ρ x` lie in it and form the internal Jordan decomposition
there, which is the image of the internal Jordan decomposition of `x`
(`LieEquiv.map_jordanDecomposition`). That ad-nilpotent elements act nilpotently holds in an
arbitrary finite-dimensional representation (`TauCeti.isNilpotent_apply_of_isNilpotent_ad`); this
file does not treat semisimple parts in representations with a nonzero kernel.

## Main results

* `LieSubalgebra.isSemisimple_ad_of_isSemisimple_ad`: an element of a Lie subalgebra that is
  ad-semisimple in the ambient Lie algebra is ad-semisimple in the subalgebra.
* `LieSubalgebra.mem_of_isNilpotent_of_add_mem`, `LieSubalgebra.mem_of_isSemisimple_of_add_mem`:
  a Killing Lie subalgebra of `𝔤𝔩(V)` contains the Jordan–Chevalley parts of its elements.
* `LieHom.apply_nilpotentPart_eq`, `LieHom.apply_semisimplePart_eq`: a faithful representation
  carries the internal Jordan decomposition of `x` to the Jordan–Chevalley decomposition of `ρ x`.
* `LieHom.isSemisimple_apply_semisimplePart`: under a faithful representation the image of the
  semisimple part is semisimple.
* `LieHom.isSemisimple_apply_iff_isSemisimple_ad`, `LieHom.isNilpotent_apply_iff_isNilpotent_ad`:
  under a faithful representation, ad-semisimplicity and ad-nilpotence are detected by the image.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.4
  (Theorem and Corollary).
-/

public section

open LieAlgebra LieModule Module Module.End

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

/-- An element of a Lie subalgebra whose adjoint action on the ambient Lie algebra is semisimple
also has semisimple adjoint action on the subalgebra. This is the semisimple analogue of
`LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad`. -/
theorem isSemisimple_ad_of_isSemisimple_ad {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (L' : LieSubalgebra R L) {x : L'} (h : (ad R L x).IsSemisimple) : (ad R L' x).IsSemisimple := by
  have hp : L'.toSubmodule ∈ (ad R L x).invtSubmodule :=
    (mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun y hy ↦ L'.lie_mem x.2 hy
  -- The restriction of `ad x` to `L'` is, elementwise by definition, the adjoint action on `L'`.
  exact (LinearEquiv.isSemisimple_iff _ _ (LinearEquiv.refl R L') (by ext; rfl)).1 (h.restrict hp)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (L : LieSubalgebra K (Module.End K V))

/-- Every element of `L` preserves each `L`-submodule of `V`. -/
private theorem apply_mem_of_mem {z : Module.End K V} (hz : z ∈ L) (W : LieSubmodule K L V) :
    ∀ w ∈ W, z w ∈ W :=
  fun w hw ↦ by simpa using W.lie_mem (x := ⟨z, hz⟩) hw

/-- Every element of `L` has trace zero on each `L`-submodule of `V`, because `L` is perfect. -/
private theorem trace_restrict_eq_zero_of_mem [FiniteDimensional K V] [IsKilling K L]
    {z : Module.End K V} (hz : z ∈ L) (W : LieSubmodule K L V) :
    LinearMap.trace K W (z.restrict (apply_mem_of_mem L hz W)) = 0 := by
  -- The restriction of `z` to `W` is, by definition, the action of `z` on the Lie module `W`.
  have hzW : z.restrict (apply_mem_of_mem L hz W) = toEnd K L W ⟨z, hz⟩ := rfl
  rw [hzW]
  refine trace_toEnd_eq_zero_of_mem_lcs K L W le_rfl
    (derivedSeries_le_lowerCentralSeries K L 1 ?_)
  rw [TauCeti.derivedSeries_one_eq_top_of_isKilling]
  exact LieSubmodule.mem_top _

variable [FiniteDimensional K V] [CharZero K] [IsAlgClosed K] [IsKilling K L]

/-- An endomorphism `q` of `V` that commutes with `L`, preserves every `L`-submodule and has trace
zero on each of them vanishes: by Schur's lemma it is a scalar on each irreducible summand of `V`,
and the trace condition forces that scalar to be zero. -/
private theorem eq_zero_of_forall_commute (q : Module.End K V) (hcomm : ∀ z ∈ L, Commute z q)
    (hinv : ∀ W : LieSubmodule K L V, ∀ w ∈ W, q w ∈ W)
    (htr : ∀ W : LieSubmodule K L V, LinearMap.trace K W (q.restrict (hinv W)) = 0) :
    q = 0 := by
  obtain ⟨k, N, hint, hirr⟩ := TauCeti.exists_isInternal_isIrreducible_of_isKilling K L V
  suffices h : ∀ i, (N i : Submodule K V) ≤ LinearMap.ker q by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hint.submodule_iSup_eq_top]
    exact iSup_le h
  intro i
  have := hirr i
  have := LieModule.nontrivial_of_isIrreducible K L (N i)
  -- The restriction of `q` to the irreducible summand `N i` is a morphism of `L`-modules.
  let f : N i →ₗ⁅K,L⁆ N i :=
    { q.restrict (hinv (N i)) with
      map_lie' := fun {z w} ↦ Subtype.ext <| by
        simp only [LinearMap.toFun_eq_coe, LieSubmodule.coe_bracket, LinearMap.coe_restrict_apply,
          coe_bracket_of_module, Module.End.lie_apply]
        exact congr($((hcomm z z.2).eq) (w : V)).symm }
  obtain ⟨c, hc⟩ := TauCeti.exists_forall_apply_eq_smul K L (N i) f
  have hres : q.restrict (hinv (N i)) = c • LinearMap.id := LinearMap.ext hc
  have hc0 : c = 0 := by
    have := htr (N i)
    rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_right (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  intro v hv
  simpa [LinearMap.coe_restrict_apply, hc0] using congr(($hres ⟨v, hv⟩ : V))

/-- An endomorphism of `V` that normalizes `L`, preserves every `L`-submodule of `V` and has trace
zero on each of them lies in `L`. Split it along an `L`-stable complement of `L` in `𝔤𝔩(V)`: the
complementary component commutes with `L`, so it vanishes by `eq_zero_of_forall_commute`. -/
private theorem mem_of_forall_lie_mem (y : Module.End K V) (hnorm : ∀ z ∈ L, ⁅y, z⁆ ∈ L)
    (hinv : ∀ W : LieSubmodule K L V, ∀ w ∈ W, y w ∈ W)
    (htr : ∀ W : LieSubmodule K L V, LinearMap.trace K W (y.restrict (hinv W)) = 0) : y ∈ L := by
  obtain ⟨Q, hQ⟩ := TauCeti.exists_isCompl_of_isKilling L.toLieSubmodule
  obtain ⟨a, ha, q, hq, rfl⟩ :=
    (LieSubmodule.mem_sup _ _ _).1 (hQ.sup_eq_top ▸ LieSubmodule.mem_top y)
  have ha' : a ∈ L := ha
  suffices q = 0 by simpa [this] using ha'
  have hqW (W : LieSubmodule K L V) (w : V) (hw : w ∈ W) : q w ∈ W := by
    simpa using W.sub_mem (hinv W w hw) (apply_mem_of_mem L ha' W w hw)
  refine eq_zero_of_forall_commute L q ?_ hqW fun W ↦ ?_
  · -- The bracket of `q` with `L` lies in both `L` and `Q`, hence vanishes.
    intro z hz
    have hzQ : ⁅z, q⁆ ∈ Q := by simpa using Q.lie_mem (x := ⟨z, hz⟩) hq
    have hzL : ⁅z, q⁆ ∈ L := by
      have : ⁅z, q⁆ = -⁅a + q, z⁆ - ⁅z, a⁆ := by
        rw [add_lie, ← lie_skew z q, ← lie_skew z a]
        abel
      rw [this]
      exact L.sub_mem (L.neg_mem (hnorm z hz)) (L.lie_mem hz ha')
    have h0 : ⁅z, q⁆ ∈ L.toLieSubmodule ⊓ Q := ⟨(L.mem_toLieSubmodule _).2 hzL, hzQ⟩
    rw [hQ.inf_eq_bot, LieSubmodule.mem_bot] at h0
    rwa [LieRing.of_associative_ring_bracket, sub_eq_zero] at h0
  · have hsplit : q.restrict (hqW W) =
        (a + q).restrict (hinv W) - a.restrict (apply_mem_of_mem L ha' W) := by
      ext w
      simp [LinearMap.coe_restrict_apply]
    rw [hsplit, map_sub, htr W, trace_restrict_eq_zero_of_mem L ha' W, sub_zero]

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

variable {K L V : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

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

/-- Under a faithful finite-dimensional representation, an element of a Killing Lie algebra over an
algebraically closed field of characteristic zero is ad-nilpotent exactly when its image is
nilpotent. -/
theorem isNilpotent_apply_iff_isNilpotent_ad (ρ : L →ₗ⁅K⁆ Module.End K V)
    (hρ : Function.Injective ρ) (x : L) :
    IsNilpotent (ρ x) ↔ IsNilpotent (ad K L x) := by
  refine ⟨fun h ↦ ?_, TauCeti.isNilpotent_apply_of_isNilpotent_ad⟩
  rw [← semisimplePart_eq_zero_iff K, ← hρ.eq_iff, map_zero]
  exact ρ.apply_semisimplePart_eq hρ (Commute.zero_right _) h isSemisimple_zero (add_zero _).symm

end LieHom
