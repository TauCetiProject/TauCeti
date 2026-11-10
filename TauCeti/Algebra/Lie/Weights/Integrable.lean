/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Spectrum
public import TauCeti.Algebra.Lie.Sl2.WeightMultiplicity
public import TauCeti.Algebra.Lie.Submodule.LocallyFinite
public import TauCeti.LinearAlgebra.Eigenspace.Separation
public import Mathlib.Algebra.Lie.Weights.Killing

/-!
# The weights of an integrable module are stable under the root reflections

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `α` be a root. A module
`M` is **integrable along `α`** when every vector of `M` lies in a finitely generated subspace
stable under the `sl₂` triple of `α`, that is when
`TauCeti.locallyFiniteSubmodule K M (t.toLieSubalgebra K) = ⊤` for such a triple `t`. This file
proves that the weights of an integrable module are stable under the reflection `s_α`.

`M` is **not** assumed finite-dimensional, and that is the point. For a finite-dimensional module
`TauCeti/Algebra/Lie/Weights/WeylInvariance.lean` already proves the stronger statement that the
reflections preserve the weight *multiplicities*. But for an irreducible highest weight module
`L(λ)` finite-dimensionality is what has to be proved, and what is available beforehand is
integrability (`TauCeti/Algebra/Lie/HighestWeight/Integrable.lean`). Reflection stability of the
weight support, together with the weight cone `λ - Q⁺`, is what confines those weights to a finite
set.

## The argument

Fix a weight `χ` of `M`, a nonzero vector `v` of `M_χ`, and a finitely generated subspace `N`
containing `v` and stable under the `sl₂` triple of `α`. The subspace

`W = ⨆ k : ℤ, (M_{k α + χ} ⊓ N)`

is a finite-dimensional module over that triple: the raising and lowering vectors move
`M_{k α + χ}` to `M_{(k ± 1) α + χ}` and preserve `N`, while `W ≤ N` is finite-dimensional because
`N` is. So the rank-one theory applies to `W`, in two ways.

* The Cartan element `α^∨` acts diagonalizably on a finite-dimensional module over an `sl₂` triple
  (`TauCeti.iSup_eigenspace_toEnd_eq_top`), with integer eigenvalues
  (`TauCeti.exists_int_of_hasEigenvalue`). Diagonalizable endomorphisms are semisimple
  (`TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`), so the generalized eigenvectors lying in `W`
  are honest eigenvectors, and `χ (α^∨) = m` is an integer.
* Its eigenspaces at opposite eigenvalues have equal dimension
  (`TauCeti.finrank_eigenspace_toEnd_neg`). The eigenvalue `m` is attained, by `v`, so `-m` is
  attained too.

An eigenvector for `-m` inside `W` has to lie in the summand `M_{-m α + χ} ⊓ N`, because `α^∨` acts
on the summand `M_{k α + χ} ⊓ N` by `2 k + m` and these scalars are distinct
(`TauCeti.biSup_inf_eigenspace_eq_self`). That summand is therefore nonzero, and
`-m α + χ = χ - χ(α^∨) α` is the reflection of `χ`.

## Main results

* `TauCeti.exists_int_apply_coroot_of_genWeightSpace_ne_bot`: a weight of a module integrable along
  `α` takes an integer value on the coroot `α^∨`, so the reflection statement below needs no
  integrality hypothesis.
* `TauCeti.genWeightSpace_sub_apply_coroot_smul_ne_bot`: **the weights of a module integrable along
  `α` are stable under the reflection `s_α`**, and
  `TauCeti.genWeightSpace_sub_apply_coroot_smul_eq_bot_iff` records the resulting equivalence, the
  reflection being an involution.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., §3.6.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

/-! ### Reflection stability of the weights of an integrable module -/

section Killing

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {α : Weight K H L} {χ : H → K} {h e f : L}

omit [CharZero K] [IsKilling K L] [FiniteDimensional K L] [IsTriangularizable K H L] in
/-- A root vector `x` that preserves a subspace `N` and shifts the `α`-string of `χ` by a multiple
of `α` preserves the sum `⨆ k, P k` of the pieces `M_{k α + χ} ⊓ N` of the string. -/
private theorem lie_mem_iSup_of_mem_rootSpace {N : Submodule K M} (P : ℤ → Submodule K M)
    (hP : ∀ k : ℤ, P k = (genWeightSpace M (k • ⇑α + χ)).toSubmodule ⊓ N)
    {x : L} {β : H → K} (hx : x ∈ rootSpace H β) (hNx : ∀ w ∈ N, ⁅x, w⁆ ∈ N)
    (hjump : ∀ k : ℤ, ∃ j : ℤ, β + (k • ⇑α + χ) = j • ⇑α + χ) {u : M}
    (hu : u ∈ ⨆ k : ℤ, P k) : ⁅x, u⁆ ∈ ⨆ k : ℤ, P k := by
  have hle : (⨆ k : ℤ, P k) ≤ (⨆ k : ℤ, P k).comap (toEnd K L M x) := by
    refine iSup_le fun k w hw ↦ ?_
    obtain ⟨j, hj⟩ := hjump k
    rw [hP] at hw
    have hmapped := mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H M β
      (k • ⇑α + χ) hx hw.1
    rw [hj] at hmapped
    exact le_iSup P j (by rw [hP]; exact ⟨hmapped, hNx w hw.2⟩)
  simpa using hle hu

/-- The pieces `M_{k α + χ} ⊓ N` of the `α`-string of `χ` lie in the eigenspaces `χ(α^∨) + 2 k`
of the coroot, provided generalized eigenvectors of the coroot in a subspace `W` containing them
are honest eigenvectors. -/
private theorem string_inf_le_eigenspace (hα : α.IsNonZero) {N W : Submodule K M}
    (hPW : ∀ k : ℤ, (genWeightSpace M (k • ⇑α + χ)).toSubmodule ⊓ N ≤ W)
    (hhonest : ∀ (c : K) {u : M}, u ∈ W →
      u ∈ (toEnd K H M (IsKilling.coroot α)).maxGenEigenspace c →
        toEnd K H M (IsKilling.coroot α) u = c • u) (k : ℤ) :
    (genWeightSpace M (k • ⇑α + χ)).toSubmodule ⊓ N ≤
      (toEnd K H M (IsKilling.coroot α)).eigenspace (χ (IsKilling.coroot α) + 2 * k) := by
  intro u hu
  have hval : (k • ⇑α + χ) (IsKilling.coroot α) = χ (IsKilling.coroot α) + 2 * k := by
    simp only [Pi.add_apply, Pi.smul_apply, IsKilling.root_apply_coroot hα]
    push_cast [zsmul_eq_mul]
    ring
  have hgen : u ∈ (toEnd K H M (IsKilling.coroot α)).maxGenEigenspace
      (χ (IsKilling.coroot α) + 2 * k) := by
    obtain ⟨j, hj⟩ := (mem_genWeightSpace M (k • ⇑α + χ) u).1 hu.1 (IsKilling.coroot α)
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨j, by rwa [hval] at hj⟩
  exact Module.End.mem_eigenspace_iff.2 (hhonest _ (hPW k hu) hgen)

omit [IsTriangularizable K H L] in
/-- A nonzero vector of `⨆ k, (M_{k α + χ} ⊓ N)` on which the coroot acts by `-χ(α^∨)` lies in the
`(-m)`-th piece, where `χ(α^∨) = m`, because the coroot acts on the `k`-th piece by
`χ(α^∨) + 2 k` and these scalars are distinct. So `-m α + χ` is a weight. -/
private theorem genWeightSpace_neg_zsmul_add_ne_bot (P : ℤ → Submodule K M) {N : Submodule K M}
    (hP : ∀ k : ℤ, P k = (genWeightSpace M (k • ⇑α + χ)).toSubmodule ⊓ N)
    (hPeig : ∀ k : ℤ, P k ≤
      (toEnd K H M (IsKilling.coroot α)).eigenspace (χ (IsKilling.coroot α) + 2 * k))
    {m : ℤ} (hm : χ (IsKilling.coroot α) = (m : K)) {u : M} (huW : u ∈ ⨆ k : ℤ, P k) (hu0 : u ≠ 0)
    (huA : toEnd K H M (IsKilling.coroot α) u = (-χ (IsKilling.coroot α)) • u) :
    genWeightSpace M ((-m : ℤ) • ⇑α + χ) ≠ ⊥ := by
  have hginj : Function.Injective fun k : ℤ ↦ χ (IsKilling.coroot α) + 2 * k := by
    intro k k' hkk'
    have : (2 : K) * k = 2 * k' := by simpa only [add_right_inj] using hkk'
    exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := K)) this
  have hloc := biSup_inf_eigenspace_eq_self (s := (Set.univ : Set ℤ)) _ P
    (fun k ↦ χ (IsKilling.coroot α) + 2 * k) (fun j _ ↦ hPeig j) (Set.mem_univ (-m))
    fun j _ hj hcon ↦ hj (hginj hcon)
  have huP : u ∈ P (-m) := by
    rw [← hloc]
    refine ⟨by simpa using huW, Module.End.mem_eigenspace_iff.2 ?_⟩
    rw [huA, hm]
    push_cast
    module
  intro hbot
  have : u ∈ (genWeightSpace M ((-m : ℤ) • ⇑α + χ)).toSubmodule := ((hP _).le huP).1
  rw [hbot] at this
  exact hu0 (by simpa using this)

/-- Both statements of this file at once: for a module integrable along a nonzero root `α`, the
value of a weight `χ` on the coroot `α^∨` is an integer `m`, and `-m • α + χ` is again a weight.

The two are proved together because both come out of the same finite-dimensional module over the
`sl₂` triple of `α`, cut out of `M` by the `α`-string of `χ` and a finitely generated stable
subspace. -/
private theorem exists_int_apply_coroot_and_genWeightSpace_zsmul_add_ne_bot (hα : α.IsNonZero)
    (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤)
    (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ m : ℤ, χ (IsKilling.coroot α) = (m : K) ∧
      genWeightSpace M ((-m : ℤ) • ⇑α + χ) ≠ ⊥ := by
  classical
  have hh : h = (IsKilling.coroot α : L) := t.h_eq_coroot hα he hf
  -- a nonzero vector of the weight space, and a finitely generated stable subspace around it
  obtain ⟨v, hvmem, hv0⟩ := (Submodule.ne_bot_iff _).1
    (fun hbot ↦ hχ (by rwa [← LieSubmodule.toSubmodule_eq_bot]))
  have hvlf : v ∈ locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) := by
    rw [hlf]; trivial
  obtain ⟨N, hNfg, hNst, hvN⟩ := mem_locallyFiniteSubmodule.1 hvlf
  -- the `α`-string of `χ`, truncated to `N`
  set P : ℤ → Submodule K M := fun k ↦ (genWeightSpace M (k • ⇑α + χ)).toSubmodule ⊓ N
  set W : Submodule K M := ⨆ k : ℤ, P k with hWdef
  have hWN : W ≤ N := iSup_le fun _ ↦ inf_le_right
  have hvP : v ∈ P 0 := ⟨by simpa using hvmem, hvN⟩
  -- a root vector shifts the string by its own root and preserves `N`, hence preserves `W`
  have hWe : ∀ u ∈ W, ⁅e, u⁆ ∈ W := fun u hu ↦
    lie_mem_iSup_of_mem_rootSpace P (fun _ ↦ rfl) he (hNst e t.e_mem_toLieSubalgebra)
      (fun k ↦ ⟨k + 1, by rw [add_zsmul, one_zsmul]; abel⟩) hu
  have hWf : ∀ u ∈ W, ⁅f, u⁆ ∈ W := fun u hu ↦
    lie_mem_iSup_of_mem_rootSpace P (fun _ ↦ rfl) hf (hNst f t.f_mem_toLieSubalgebra)
      (fun k ↦ ⟨k - 1, by rw [sub_zsmul, one_zsmul]; abel⟩) hu
  -- `W` as a finite-dimensional module over the subalgebra generated by the triple
  set 𝒲 : LieSubmodule K (t.toLieSubalgebra K) M := t.lieSubmoduleOfStable W hWe hWf
  have hmem𝒲 : ∀ {u : M}, u ∈ 𝒲 ↔ u ∈ W := t.mem_lieSubmoduleOfStable W hWe hWf
  have : FiniteDimensional K N := (Submodule.fg_iff_finiteDimensional N).1 hNfg
  -- `LieSubmodule.mem_toSubmodule` is definitional, so the two subtypes below are the same type.
  have : FiniteDimensional K 𝒲 := by
    have : FiniteDimensional K (𝒲.toSubmodule : Submodule K M) := by
      rw [t.lieSubmoduleOfStable_toSubmodule W hWe hWf]
      exact Submodule.finiteDimensional_of_le hWN
    exact this
  have hhonest : ∀ (c : K) {u : M}, u ∈ W →
      u ∈ (toEnd K H M (IsKilling.coroot α)).maxGenEigenspace c →
        toEnd K H M (IsKilling.coroot α) u = c • u := fun c _ hu hgen ↦
    t.toEnd_apply_eq_smul_of_mem_maxGenEigenspace (x := IsKilling.coroot α) hh 𝒲 c (hmem𝒲.2 hu)
      hgen
  have hPeig := string_inf_le_eigenspace (χ := χ) (N := N) hα
    (fun k ↦ le_iSup P k) hhonest
  -- the eigenvalue `χ(α^∨)` is attained on `𝒲`, hence so is its negative
  obtain ⟨m, hm, u, humem, hu0, huA⟩ :=
    t.exists_int_and_toEnd_apply_eq_neg_smul (x := IsKilling.coroot α) hh 𝒲
    (hmem𝒲.2 (le_iSup P 0 hvP)) hv0 (by simpa using Module.End.mem_eigenspace_iff.1 (hPeig 0 hvP))
  exact ⟨m, hm, genWeightSpace_neg_zsmul_add_ne_bot P (fun _ ↦ rfl) hPeig hm (hmem𝒲.1 humem) hu0
    huA⟩

/-- **A weight of an integrable module is integral on the coroot.** If a module `M` is integrable
along a nonzero root `α`, in the sense that every vector lies in a finitely generated subspace
stable under an `sl₂` triple `(h, e, f)` of `α`, then every weight `χ` of `M` takes an integer
value on the coroot `α^∨`.

This is the rank-one integrality statement for a module that is not assumed finite-dimensional:
the string of `χ` truncated to a stable finitely generated subspace is a finite-dimensional module
over the triple, and `TauCeti.exists_int_of_hasEigenvalue` applies to it. For a finite-dimensional
module `TauCeti.exists_int_apply_coroot` says the same with no integrability hypothesis. -/
theorem exists_int_apply_coroot_of_genWeightSpace_ne_bot (hα : α.IsNonZero)
    (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤)
    (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ m : ℤ, χ (IsKilling.coroot α) = (m : K) := by
  obtain ⟨m, hm, -⟩ :=
    exists_int_apply_coroot_and_genWeightSpace_zsmul_add_ne_bot hα t he hf hlf hχ
  exact ⟨m, hm⟩

/-- **The weights of an integrable module are stable under the root reflections.** Let `α` be a
nonzero root with `sl₂` triple `(h, e, f)`, and let `M` be a module integrable along `α`: every
vector of `M` lies in a finitely generated subspace stable under the triple. Then the reflection
`s_α χ = χ - χ(α^∨) α` of a weight of `M` is again a weight of `M`.

`M` is not assumed finite-dimensional. For a finite-dimensional module
`TauCeti.finrank_weightSpace_sub_apply_coroot_smul` gives the stronger conclusion that the
reflection preserves the multiplicity. -/
theorem genWeightSpace_sub_apply_coroot_smul_ne_bot (hα : α.IsNonZero) (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤)
    (hχ : genWeightSpace M χ ≠ ⊥) :
    genWeightSpace M (χ - χ (IsKilling.coroot α) • ⇑α) ≠ ⊥ := by
  obtain ⟨m, hm, hne⟩ :=
    exists_int_apply_coroot_and_genWeightSpace_zsmul_add_ne_bot hα t he hf hlf hχ
  have hrewrite : χ - χ (IsKilling.coroot α) • ⇑α = (-m : ℤ) • ⇑α + χ := by
    rw [hm, ← Int.cast_smul_eq_zsmul K (-m) (⇑α : H → K)]
    push_cast
    module
  rwa [hrewrite]

/-- **The weights of an integrable module are exactly the reflections of its weights.** With the
hypotheses of `TauCeti.genWeightSpace_sub_apply_coroot_smul_ne_bot`, a form `χ` on the Cartan
subalgebra is a weight of `M` exactly when its reflection `s_α χ` is: the reflection is an
involution, so the forward implication applies in both directions. -/
theorem genWeightSpace_sub_apply_coroot_smul_eq_bot_iff (hα : α.IsNonZero) (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤) :
    genWeightSpace M (χ - χ (IsKilling.coroot α) • ⇑α) = ⊥ ↔ genWeightSpace M χ = ⊥ := by
  set ψ : H → K := χ - χ (IsKilling.coroot α) • ⇑α with hψdef
  have hψval : ψ (IsKilling.coroot α) = -χ (IsKilling.coroot α) := by
    simp only [hψdef, Pi.sub_apply, Pi.smul_apply, IsKilling.root_apply_coroot hα, smul_eq_mul]
    ring
  have hinv : ψ - ψ (IsKilling.coroot α) • ⇑α = χ := by
    rw [hψval, hψdef]
    module
  refine not_iff_not.1 ⟨fun hψ ↦ ?_, fun hχ ↦ ?_⟩
  · have := genWeightSpace_sub_apply_coroot_smul_ne_bot (χ := ψ) hα t he hf hlf hψ
    rwa [hinv] at this
  · exact genWeightSpace_sub_apply_coroot_smul_ne_bot hα t he hf hlf hχ

end Killing

end TauCeti
