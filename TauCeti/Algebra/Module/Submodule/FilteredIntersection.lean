/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import TauCeti.Order.Directed

/-!
# An Artinian submodule meets a filtered intersection at a finite stage

Let `F` be a downward-directed family of submodules of a module `M` — a filtration `F 0 ≥ F 1 ≥ ⋯`
is the typical case — and let `W` be a submodule of `M` that is Artinian, for instance a
finite-dimensional subspace of an infinite-dimensional vector space. The traces `W ⊓ F i` are again
downward directed, and they live in the Artinian lattice of submodules of `W`, so they cannot
descend forever: one of them already equals the trace `W ⊓ ⨅ j, F j` of the whole intersection. In
particular, if the family intersects in `⊥`, then `W ⊓ F i = ⊥` for some single `i`.

Nothing is assumed about `M` itself; that is the point. Mathlib's stabilization results for
descending chains — `IsArtinian.monotone_stabilizes` and `Module.End.eventually_iInf_range_pow_eq`
— all require the ambient module to be Artinian, which fails in the intended applications, where
`M` is an infinite-dimensional algebra and only the subspace being separated is finite-dimensional.

The lattice-theoretic core is `Directed.exists_eq_iInf` in
`TauCeti/Order/Directed.lean`; everything here is its transport along `Submodule.comap W.subtype`,
which turns the traces on `W` into honest submodules of `W` and so makes `IsArtinian R W`
applicable.

## Main results

* `Submodule.exists_inf_eq_inf_iInf_of_directed`: the trace of a downward-directed family of
  submodules on an Artinian submodule `W` attains the trace of the infimum, with no hypothesis on
  the ambient module.
* `Submodule.exists_disjoint_of_directed`: consequently `W` is disjoint from a single member of the
  family as soon as it is disjoint from their infimum.
* `Submodule.exists_forall_inf_eq_inf_iInf_of_antitone` and
  `Submodule.exists_forall_inf_eq_bot_of_antitone`: for an antitone filtration indexed by a
  directed order the trace is *eventually* constant, not merely constant at one index.
* `LinearMap.exists_mkQ_comp_injective_of_directed`: the form the applications use — an embedding
  of an Artinian module into `M` stays injective after passing to the quotient by a single member
  of a family whose infimum is `⊥`.
* `Ideal.exists_forall_inf_restrictScalars_pow_eq_bot`: the specialization to the powers of a
  (one- or two-sided) ideal of an algebra, viewed as submodules over the base ring.
-/

public section

universe u v w

namespace Submodule

section Semiring

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Sort*}

/-- **The trace of a downward-directed family of submodules on an Artinian submodule attains the
trace of the infimum.**

The ambient module `M` is arbitrary; only `W` is Artinian. This is the statement wanted when `M` is
an infinite-dimensional algebra and `W` is a finite-dimensional subspace of it, where applying
`Directed.exists_eq_iInf` to the lattice `Submodule R M` itself is not possible. -/
theorem exists_inf_eq_inf_iInf_of_directed [Nonempty ι] (W : Submodule R M) [IsArtinian R W]
    (F : ι → Submodule R M) (hF : Directed (· ≥ ·) F) : ∃ i, W ⊓ F i = W ⊓ ⨅ j, F j := by
  obtain ⟨i, hi⟩ := Directed.exists_eq_iInf (f := fun j ↦ (F j).comap W.subtype)
    fun j k ↦ (hF j k).imp fun _ hl ↦ ⟨comap_mono hl.1, comap_mono hl.2⟩
  refine ⟨i, ?_⟩
  have h := congrArg (map W.subtype) hi
  rwa [map_comap_subtype, ← comap_iInf, map_comap_subtype] at h

/-- **An Artinian submodule disjoint from a filtered intersection is already disjoint from one
member of the family.** -/
theorem exists_disjoint_of_directed [Nonempty ι] (W : Submodule R M) [IsArtinian R W]
    (F : ι → Submodule R M) (hF : Directed (· ≥ ·) F) (hW : Disjoint W (⨅ j, F j)) :
    ∃ i, Disjoint W (F i) := by
  obtain ⟨i, hi⟩ := exists_inf_eq_inf_iInf_of_directed W F hF
  exact ⟨i, disjoint_iff.mpr (hi.trans (disjoint_iff.mp hW))⟩

end Semiring

section Antitone

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

/-- **The trace of an antitone filtration on an Artinian submodule is eventually the trace of the
intersection.**

Unlike `Submodule.exists_inf_eq_inf_iInf_of_directed`, which produces one index, monotonicity makes
the conclusion hold from that index onwards. -/
theorem exists_forall_inf_eq_inf_iInf_of_antitone (W : Submodule R M) [IsArtinian R W]
    (F : ι → Submodule R M) (hF : Antitone F) :
    ∃ i, ∀ j, i ≤ j → W ⊓ F j = W ⊓ ⨅ k, F k := by
  obtain ⟨i, hi⟩ := exists_inf_eq_inf_iInf_of_directed W F
    fun j k ↦ (exists_ge_ge j k).imp fun _ h ↦ ⟨hF h.1, hF h.2⟩
  refine ⟨i, fun j hij ↦ le_antisymm ?_ (inf_le_inf_left W (iInf_le F j))⟩
  exact hi ▸ inf_le_inf_left W (hF hij)

/-- **An antitone filtration with zero intersection eventually misses an Artinian submodule.**

This is the separation step in the form its consumers use: `W` is a finite-dimensional subspace,
`F` is a filtration of the ambient module by submodules with `⨅ k, F k = ⊥`, and the conclusion
exhibits a stage at which `W` is separated. -/
theorem exists_forall_inf_eq_bot_of_antitone (W : Submodule R M) [IsArtinian R W]
    (F : ι → Submodule R M) (hF : Antitone F) (h : ⨅ k, F k = ⊥) :
    ∃ i, ∀ j, i ≤ j → W ⊓ F j = ⊥ := by
  obtain ⟨i, hi⟩ := exists_forall_inf_eq_inf_iInf_of_antitone W F hF
  exact ⟨i, fun j hij ↦ by rw [hi j hij, h, inf_bot_eq]⟩

end Antitone

end Submodule

namespace LinearMap

variable {R : Type u} {M : Type v} {N : Type w}
variable [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι : Sort*}

/-- **An embedding of an Artinian module survives the quotient by a single member of a family whose
intersection is zero.**

Applied to the canonical embedding of a finite-dimensional Lie algebra into its universal
enveloping algebra, this is the statement that the algebra is separated by one finite stage of a
filtration, which is how a faithful representation on a quotient is obtained. -/
theorem exists_mkQ_comp_injective_of_directed [Nonempty ι] [IsArtinian R N] (f : N →ₗ[R] M)
    (hf : Function.Injective f) (F : ι → Submodule R M) (hF : Directed (· ≥ ·) F)
    (h : ⨅ j, F j = ⊥) : ∃ i, Function.Injective ((F i).mkQ ∘ₗ f) := by
  obtain ⟨i, hi⟩ := Submodule.exists_disjoint_of_directed (range f) F hF (h ▸ disjoint_bot_right)
  rw [← Submodule.ker_mkQ (F i)] at hi
  -- The quotient map is injective on `range f`, and `f` is injective onto its range.
  exact ⟨i, fun x y hxy ↦
    hf (disjoint_ker_iff_injOn.mp hi (mem_range_self f x) (mem_range_self f y) hxy)⟩

end LinearMap

namespace Ideal

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/-- **The powers of an ideal whose intersection is zero are eventually disjoint from an Artinian
submodule of the algebra.**

No commutativity of `A` and no two-sidedness of `I` is needed: the powers of a left ideal are
antitone, and the statement concerns their underlying `R`-submodules. This is the shape taken by
the separation of a finite-dimensional Lie algebra from the powers of the central ideal of its
universal enveloping algebra. -/
theorem exists_forall_inf_restrictScalars_pow_eq_bot (I : Ideal A) (W : Submodule R A)
    [IsArtinian R W] (h : ⨅ n : ℕ, I ^ n = ⊥) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → W ⊓ (I ^ m).restrictScalars R = ⊥ := by
  refine Submodule.exists_forall_inf_eq_bot_of_antitone W _
    (fun _ _ hmn ↦ Submodule.restrictScalars_mono R (pow_le_pow_right hmn)) ?_
  rw [← Submodule.restrictScalars_iInf, h, Submodule.restrictScalars_bot]

end Ideal
