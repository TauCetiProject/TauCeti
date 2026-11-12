/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.Sl2.Spectrum
public import TauCeti.Algebra.Lie.Weights.Semisimple
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# The Cartan subalgebra acts diagonalizably, and weight spaces are honest

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a split Cartan subalgebra, and let `M` be a
finite-dimensional `L`-module. This file proves that **every `x : H` acts on `M` by a semisimple
endomorphism**, so that Mathlib's *generalized* weight spaces `LieModule.genWeightSpace M χ` are
the *honest* simultaneous eigenspaces `LieModule.weightSpace M χ`. The split Cartan action
is triangularizable on `M`, and these spaces form its internal direct sum.

The route is the rank-one reduction, not the abstract Jordan decomposition. A nonzero root `α`
carries an `sl₂` triple whose Cartan element is the coroot `α^∨`, and the `sl₂` engine already
knows that such an element acts diagonalizably
(`TauCeti.iSup_eigenspace_toEnd_eq_top`), hence semisimply
(`TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`). The coroots span `H`, and `H` is
abelian, so the operators they give are commuting semisimple endomorphisms, and semisimplicity
passes to their span (`Module.End.IsSemisimple.add_of_commute`,
`Module.End.IsSemisimple.of_mem_adjoin_singleton`).

In particular the proof uses only complete reducibility **for `sl₂`**, which is where
`TauCeti.iSup_eigenspace_toEnd_eq_top` comes from, and not Weyl's complete reducibility for `L`.
That is what keeps the highest-weight theory free of circularity: the honest weight-space
decomposition is available before Weyl's theorem, whose usual proof consumes it.

Triangularizability of `M` follows from the split Cartan hypothesis: the coroots act
diagonalizably and commute, so their simultaneous eigenspaces span `M`. Since the coroots span
`H`, these are simultaneous eigenspaces for all of `H`. Thus the spanning, internal-direct-sum
and trace formulas need no additional hypothesis on `M`.

## Main results

* `TauCeti.nonempty_weight`: a nonzero finite-dimensional triangularizable module has a weight.
* `TauCeti.isInternal_genWeightSpace`: a finite-dimensional triangularizable module is the internal
  direct sum of its *generalized* weight spaces. This needs no diagonalizability and is the form
  the dimension counts consume; the honest-weight-space refinement is below.
* `TauCeti.eq_zero_of_forall_genWeightSpace`: a linear functional vanishing on every generalized
  weight space is zero.
* `TauCeti.iSup_eigenspace_toEnd_coroot_eq_top`: the eigenspaces of a nonzero coroot span every
  finite-dimensional module.
* `TauCeti.isSemisimple_toEnd_coroot`: a coroot acts semisimply on a finite-dimensional module.
* `TauCeti.isSemisimple_toEnd_cartan`: **every element of the Cartan subalgebra acts semisimply.**
* `TauCeti.instIsTriangularizableCartan`: the split Cartan action is triangularizable on every
  finite-dimensional module.
* `TauCeti.genWeightSpace_eq_weightSpace`: **the generalized weight spaces are honest weight
  spaces**, with `TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul` the pointwise form: membership
  is the eigenvector equation `⁅x, m⁆ = χ x • m` for every `x : H`.
* `TauCeti.iSup_weightSpace_eq_top` and `TauCeti.isInternal_weightSpace`: the honest weight spaces
  span `M`, and `M` is their internal direct sum, so `χ ↦ finrank (weightSpace M χ)` counts honest
  multiplicities.
* `TauCeti.trace_toEnd_pow_eq_sum_finrank_nsmul`: `tr (ρ_M(h) ^ m) = ∑_χ dim M_χ · χ(h) ^ m`, the
  trace of a power of a Cartan element as a power sum of the weights.
* `TauCeti.eq_zero_of_genWeightSpace_ne_bot_of_isTrivial`: a trivial module has no weight but
  zero. This needs neither diagonalizability nor the Cartan hypothesis, and is stated for an
  arbitrary nilpotent Lie algebra acting trivially.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.4 and §20.1.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

/-! ### Existence of a weight -/

section Triangularizable

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]

/-- A nonzero finite-dimensional triangularizable module has at least one weight: the *generalized*
weight spaces span it (`LieModule.iSup_genWeightSpace_eq_top'`), and an empty supremum is `⊥`.
`LieModule.Weight` is by definition indexed by the linear forms whose generalized weight space is
nonzero, so no honest-weight-space hypothesis is available or needed here; nilpotency of `L` is
carried only because `LieModule.Weight` demands it.

Mathlib performs this step inside the proof of
`LieModule.exists_nontrivial_weightSpace_of_isNilpotent` rather than naming it. -/
theorem nonempty_weight [IsTriangularizable K L M] [Nontrivial M] : Nonempty (Weight K L M) := by
  by_contra! contra
  simpa only [iSup_of_empty, bot_ne_top] using iSup_genWeightSpace_eq_top' K L M

/-! ### The generalized weight-space decomposition -/

/-- **The generalized weight-space decomposition.** A finite-dimensional triangularizable module is
the internal direct sum of its generalized weight spaces, indexed by all of its weights. This is
Mathlib's `LieModule.iSupIndep_genWeightSpace'` and `LieModule.iSup_genWeightSpace_eq_top'`
packaged as a `DirectSum.IsInternal`, which is the form the dimension counts consume. -/
theorem isInternal_genWeightSpace [IsTriangularizable K L M] [DecidableEq (Weight K L M)] :
    DirectSum.IsInternal fun χ : Weight K L M ↦ (genWeightSpace M (χ : L → K)).toSubmodule := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [LieSubmodule.iSupIndep_toSubmodule]
    exact iSupIndep_genWeightSpace' K L M
  · rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top' K L M]
    simp

variable {K L M} in
/-- **A functional vanishing on every generalized weight space is zero.** The generalized weight
spaces of a finite-dimensional triangularizable module span it
(`LieModule.iSup_genWeightSpace_eq_top`), so a linear functional killing each of them kills `M`. -/
theorem eq_zero_of_forall_genWeightSpace [IsTriangularizable K L M] {g : Dual K M}
    (hg : ∀ χ : L → K, ∀ m ∈ genWeightSpace M χ, g m = 0) : g = 0 := by
  refine LinearMap.ker_eq_top.mp (top_le_iff.mp ?_)
  rw [← LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top K L M)]
  exact iSup_le fun χ m hm => hg χ m hm

end Triangularizable

/-! ### Trivial modules -/

section Trivial

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [LieModule.IsTrivial L M]

/-- **A trivial module has no weight but zero**: the only linear form with a nonzero generalized
weight space in a module on which the Lie algebra acts by zero is the zero form. -/
theorem eq_zero_of_genWeightSpace_ne_bot_of_isTrivial {chi : L → K}
    (hchi : genWeightSpace M chi ≠ ⊥) : chi = 0 := by
  rw [ne_eq, ← LieSubmodule.toSubmodule_eq_bot] at hchi
  obtain ⟨m, hm, hmne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hchi
  rw [LieSubmodule.mem_toSubmodule, mem_genWeightSpace] at hm
  funext x
  obtain ⟨k, hk⟩ := hm x
  have hx : toEnd K L M x = 0 := LinearMap.ext fun y ↦ LieModule.IsTrivial.trivial x y
  rw [hx, zero_sub, ← neg_smul, smul_pow, one_pow, LinearMap.smul_apply,
    one_apply_eq_self] at hk
  rcases smul_eq_zero.mp hk with h | h
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at h
    · simpa using (pow_eq_zero_iff hk0.ne').mp h
  · exact absurd h hmne

end Trivial

/-! ### Semisimplicity of the Cartan action -/

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- The eigenspaces of a nonzero coroot span every finite-dimensional module. -/
theorem iSup_eigenspace_toEnd_coroot_eq_top {α : Weight K H L} (hα : α.IsNonZero) :
    ⨆ μ : K, (toEnd K H M (IsKilling.coroot α)).eigenspace μ = ⊤ := by
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hsup := iSup_eigenspace_toEnd_eq_top (K := K) (M := M) ht
  rw [ht.h_eq_coroot hα he hf] at hsup
  exact hsup

/-- **A coroot acts semisimply.** The coroot `α^∨` of a weight `α` of `L` acts on a
finite-dimensional module by a semisimple endomorphism.

For a nonzero `α` this is the `sl₂` engine: `α^∨` is the Cartan element of an `sl₂` triple, whose
eigenspaces span (`TauCeti.iSup_eigenspace_toEnd_eq_top`), and a diagonalizable endomorphism is
semisimple. The coroot of a zero weight is zero. -/
theorem isSemisimple_toEnd_coroot (α : Weight K H L) :
    (toEnd K H M (IsKilling.coroot α)).IsSemisimple := by
  by_cases hα : α.IsNonZero
  · exact isSemisimple_of_iSup_eigenspace_eq_top (iSup_eigenspace_toEnd_coroot_eq_top hα)
  · rw [IsKilling.coroot_eq_zero_iff.2 (not_not.1 hα)]
    simp

private lemma mem_span_coroot_cartan (x : H) :
    x ∈ Submodule.span K (Set.range (IsKilling.rootSystem H).coroot) := by
  rw [RootPairing.IsRootSystem.span_coroot_eq_top]
  trivial

omit [FiniteDimensional K L] in
/-- **The Cartan subalgebra acts semisimply.** Every element of a Cartan subalgebra of a
Killing-semisimple Lie algebra split over the ground field acts on a finite-dimensional module
by a semisimple endomorphism.

The coroots span the Cartan subalgebra (`RootPairing.IsRootSystem.span_coroot_eq_top` for
`LieAlgebra.IsKilling.rootSystem H`) and act semisimply by
`TauCeti.isSemisimple_toEnd_coroot`; the Cartan subalgebra is abelian, so the endomorphisms they
give commute, and both a sum of commuting semisimple endomorphisms and a scalar multiple of one are
again semisimple. -/
theorem isSemisimple_toEnd_cartan (x : H) : (toEnd K H M x).IsSemisimple := by
  have := finite_of_isKilling (R := K) (L := L)
  induction mem_span_coroot_cartan x using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, rfl⟩ := hy
    exact isSemisimple_toEnd_coroot α.1
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Module.End.IsSemisimple.add_of_commute (commute_toEnd_of_isLieAbelian y z) hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact hy.of_mem_adjoin_singleton
      (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton _ _) c)

omit [FiniteDimensional K L] in
/-- A split Cartan subalgebra acts triangularizably on every finite-dimensional module. -/
instance instIsTriangularizableCartan : IsTriangularizable K H M where
  maxGenEigenspace_eq_top x := by
    have := finite_of_isKilling (R := K) (L := L)
    let f : H.root → End K M := fun α ↦ toEnd K H M (IsKilling.coroot α)
    have hdiag (α : H.root) : ⨆ μ : K, (f α).eigenspace μ = ⊤ := by
      exact iSup_eigenspace_toEnd_coroot_eq_top (H.isNonZero_coe_root α)
    have hss (α : H.root) := (isSemisimple_toEnd_coroot (M := M) α.1).isFinitelySemisimple
    have hcomm : Pairwise fun α β ↦ Commute (f α) (f β) := fun α β _ ↦
      commute_toEnd_of_isLieAbelian _ _
    -- First decompose into simultaneous eigenspaces of the coroots.
    have hsim :=
      End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        f hcomm (fun α ↦ (hss α).iSup_maxGenEigenspace_eq_top_iff.mpr (hdiag α))
    have hgen (α : H.root) (μ : K) : (f α).maxGenEigenspace μ = (f α).eigenspace μ :=
      (hss α).maxGenEigenspace_eq_eigenspace μ
    simp_rw [hgen] at hsim
    rw [← top_le_iff, ← hsim]
    refine iSup_le fun χ ↦ ?_
    -- Every Cartan element acts by a scalar on each simultaneous coroot eigenspace.
    have hscalar : ∃ μ : K, ∀ m ∈ ⨅ α, (f α).eigenspace (χ α),
        toEnd K H M x m = μ • m := by
      induction mem_span_coroot_cartan x using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨α, rfl⟩ := hy
        exact ⟨χ α, fun m hm ↦
          End.mem_eigenspace_iff.mp (iInf_le (fun β ↦ (f β).eigenspace (χ β)) α hm)⟩
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨μ, hμ⟩ := hy
        obtain ⟨ν, hν⟩ := hz
        exact ⟨μ + ν, fun m hm ↦ by simp [hμ m hm, hν m hm, add_smul]⟩
      | smul c y _ hy =>
        obtain ⟨μ, hμ⟩ := hy
        exact ⟨c * μ, fun m hm ↦ by simp [hμ m hm, mul_smul]⟩
    obtain ⟨μ, hμ⟩ := hscalar
    exact le_iSup_of_le μ fun m hm ↦
      End.eigenspace_le_maxGenEigenspace (End.mem_eigenspace_iff.mpr (hμ m hm))

/-! ### Honest weight spaces -/

omit [FiniteDimensional K L] in
/-- The generalized eigenspace of `x : H` at a scalar is an honest eigenspace. -/
@[simp]
theorem genWeightSpaceOf_eq_eigenspace (μ : K) (x : H) :
    (genWeightSpaceOf M μ x).toSubmodule = (toEnd K H M x).eigenspace μ :=
  (isSemisimple_toEnd_cartan (M := M) x).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

omit [FiniteDimensional K L] in
/-- **The generalized weight spaces are honest weight spaces.** For a finite-dimensional module over
a Killing-semisimple Lie algebra with a split Cartan subalgebra, `LieModule.genWeightSpace M χ`
is the simultaneous eigenspace `LieModule.weightSpace M χ`.

Mathlib's `LieModule.weightSpace_le_genWeightSpace` is the inclusion that holds always; this is the
reverse one, and it is exactly the diagonalizability of the Cartan action. -/
@[simp]
theorem genWeightSpace_eq_weightSpace (χ : H → K) : genWeightSpace M χ = weightSpace M χ :=
  genWeightSpace_eq_weightSpace_of_isFinitelySemisimple
    (fun x ↦ (isSemisimple_toEnd_cartan x).isFinitelySemisimple) χ

omit [FiniteDimensional K L] in
/-- **Membership of a weight space is the eigenvector equation.** An element of a
finite-dimensional module lies in the `χ`-weight space exactly when every `x : H` acts on it by the
scalar `χ x`.

This is deliberately not a `simp` lemma: `TauCeti.genWeightSpace_eq_weightSpace` already rewrites
the left-hand side to `m ∈ LieModule.weightSpace M χ`, so tagging it would leave it in
non-simp-normal form. -/
theorem mem_genWeightSpace_iff_forall_lie_eq_smul {χ : H → K} {m : M} :
    m ∈ genWeightSpace M χ ↔ ∀ x : H, ⁅(x : L), m⁆ = χ x • m := by
  rw [genWeightSpace_eq_weightSpace, mem_weightSpace]
  simp

omit [FiniteDimensional K L] in
variable (K H M) in
/-- **The honest weight spaces span.** A finite-dimensional module over a Killing-semisimple Lie
algebra with a split Cartan subalgebra is spanned by its simultaneous eigenspaces. -/
theorem iSup_weightSpace_eq_top :
    ⨆ χ : Weight K H M, weightSpace M (χ : H → K) = ⊤ := by
  simpa only [genWeightSpace_eq_weightSpace] using iSup_genWeightSpace_eq_top' K H M

omit [FiniteDimensional K L] in
variable (K H M) in
open scoped Classical in
/-- **The honest weight-space decomposition.** A finite-dimensional module over a
Killing-semisimple Lie algebra with a split Cartan subalgebra is the internal direct sum of its
simultaneous eigenspaces, so `χ ↦ finrank (weightSpace M χ)` counts honest multiplicities. -/
theorem isInternal_weightSpace :
    DirectSum.IsInternal fun χ : Weight K H M ↦ (weightSpace M (χ : H → K)).toSubmodule := by
  simpa only [genWeightSpace_eq_weightSpace] using isInternal_genWeightSpace K H M

/-! ### Traces -/

omit [FiniteDimensional K L] in
/-- **The trace of a power of a Cartan element**: `tr (ρ_M(h) ^ m) = ∑_μ dim M_μ · μ(h) ^ m`, the
sum over the weights `μ` of `M`. -/
theorem trace_toEnd_pow_eq_sum_finrank_nsmul (h : H) (m : ℕ) :
    LinearMap.trace K M (toEnd K H M h ^ m) =
      ∑ chi : Weight K H M, finrank K (genWeightSpace M chi) • chi h ^ m := by
  classical
  -- the weight space of `chi` is an honest eigenspace, on which `h` acts by the scalar `chi h`
  have hact (chi : Weight K H M) (n : ℕ) (x : M) (hx : x ∈ genWeightSpace M chi) :
      (toEnd K H M h ^ n) x = chi h ^ n • x := by
    rw [genWeightSpace_eq_weightSpace, mem_weightSpace] at hx
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, toEnd_apply_apply, hx, smul_smul,
        pow_succ]
  have hmaps (chi : Weight K H M) : Set.MapsTo (toEnd K H M h ^ m)
      (genWeightSpace M chi) (genWeightSpace M chi) := fun x hx ↦ by
    rw [SetLike.mem_coe, hact chi m x hx]
    exact Submodule.smul_mem _ _ hx
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_genWeightSpace K H M) hmaps]
  refine Finset.sum_congr rfl fun chi _ ↦ ?_
  have hres : (toEnd K H M h ^ m).restrict (hmaps chi) = chi h ^ m • LinearMap.id :=
    LinearMap.ext fun x ↦ Subtype.ext (hact chi m x x.2)
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, nsmul_eq_mul, mul_comm,
    LieSubmodule.finrank_toSubmodule]

end TauCeti
