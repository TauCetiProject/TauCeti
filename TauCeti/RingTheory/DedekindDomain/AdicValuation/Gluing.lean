/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.FaithfullyFlat
import TauCeti.Algebra.Module.Lattice
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation

/-!
# Gluing submodules from prescribed completions

Let `R` be a Dedekind domain with fraction field `K`, and let `V` be a `K`-vector space. For each
height-one prime `v` of `R` write `𝒪_v = v.adicCompletionIntegers K`. Given an `𝒪_v`-submodule
`L v` of `𝒪_v ⊗[R] V` for every `v`, the elements of `V` whose image lies in every `L v` form an
`R`-submodule `glueCompletions K L` of `V`. It is the largest `R`-submodule whose completions
`M.baseChange 𝒪_v` lie in the `L v`.

The main result is that the gluing recovers the prescribed local data as soon as it is large
enough to span: if `glueCompletions K L` spans `V` over `K` (for instance, if some spanning
`R`-submodule `Λ` has `Λ.baseChange 𝒪_v ≤ L v` for every `v`), then its completion at every `v`
is exactly `L v`. The proof is an approximation argument: an element of `L v` is approximated
modulo the completion of the gluing by the image of a global vector that is integral at every
other place, using the approximation theorem
`IsDedekindDomain.HeightOneSpectrum.exists_forall_sub_mem_span_singleton`.

Combined with the fact that submodules are determined by their completions
(`TauCeti.eq_iff_forall_baseChange_adicCompletionIntegers_eq`), this is the local–global
correspondence for lattices over a Dedekind domain: lattices are glued from their completions, and
the glued lattice is the unique one with the prescribed completions. It is the input for the
lattices `B ∩ ∏_v α_v Λ_v` attached to ideles of an order.

## Main definitions

* `TauCeti.glueCompletions K L`: the elements of `V` lying in `L v` after completion at every `v`.

## Main results

* `TauCeti.le_glueCompletions_iff`: `M ≤ glueCompletions K L` if and only if every completion of
  `M` lies in the corresponding `L v`.
* `TauCeti.exists_sub_tmul_mem_baseChange_and_forall_ne`: strong approximation for a spanning
  submodule `N`: every element of `𝒪_v ⊗[R] V` is congruent modulo `N.baseChange 𝒪_v` to the image
  of a vector whose image lies in `N.baseChange 𝒪_w` at every other place `w`.
* `TauCeti.baseChange_glueCompletions`: if the gluing spans `V`, its completion at every `v` is
  `L v`.
* `TauCeti.glueCompletions_baseChange`: gluing the completions of a submodule gives it back.
* `TauCeti.eq_glueCompletions_iff`: if the gluing spans `V`, it is the unique submodule with
  completions `L v`.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
  Chapter 9 (the local–global dictionary for lattices).
* A. Fröhlich, *Locally free modules over arithmetic orders*, J. Reine Angew. Math. 274/275
  (1975), 112–138, §2.
-/

public section

open TensorProduct IsDedekindDomain Submodule

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V]

/-- **Gluing local submodules.** Given an `𝒪_v`-submodule `L v` of `𝒪_v ⊗[R] V` at every
height-one prime `v`, the `R`-submodule of those `x : V` with `1 ⊗ₜ x ∈ L v` for every `v`. -/
noncomputable def glueCompletions
    (L : ∀ v : HeightOneSpectrum R,
      Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K ⊗[R] V)) :
    Submodule R V :=
  ⨅ v, ((L v).restrictScalars R).comap (TensorProduct.mk R (v.adicCompletionIntegers K) V 1)

variable {K}
variable {L : ∀ v : HeightOneSpectrum R,
  Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K ⊗[R] V)}

@[simp]
theorem mem_glueCompletions {x : V} :
    x ∈ glueCompletions K L ↔
      ∀ v : HeightOneSpectrum R, (1 : v.adicCompletionIntegers K) ⊗ₜ x ∈ L v := by
  simp [glueCompletions, mem_iInf]

/-- The gluing is the largest submodule whose completions lie in the prescribed local
submodules. -/
theorem le_glueCompletions_iff {M : Submodule R V} :
    M ≤ glueCompletions K L ↔
      ∀ v : HeightOneSpectrum R, M.baseChange (v.adicCompletionIntegers K) ≤ L v := by
  simp only [glueCompletions, le_iInf_iff, baseChange_le_iff_le_comap]

/-- The completion of the gluing at `v` lies in `L v`. -/
theorem baseChange_glueCompletions_le (v : HeightOneSpectrum R) :
    (glueCompletions K L).baseChange (v.adicCompletionIntegers K) ≤ L v :=
  le_glueCompletions_iff.1 le_rfl v

/-- The gluing is monotone in the local data. -/
theorem glueCompletions_mono
    {L' : ∀ v : HeightOneSpectrum R,
      Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K ⊗[R] V)}
    (h : ∀ v, L v ≤ L' v) : glueCompletions K L ≤ glueCompletions K L' :=
  le_glueCompletions_iff.2 fun v ↦ (baseChange_glueCompletions_le v).trans (h v)

variable [Module K V] [IsScalarTower R K V]

/-- **Strong approximation for a spanning submodule.** Let `N` be an `R`-submodule spanning `V`
over `K`. Every element `y` of `𝒪_v ⊗[R] V` is congruent modulo `N.baseChange 𝒪_v` to the image
`1 ⊗ₜ x` of a vector `x : V` that lies in `N.baseChange 𝒪_w` at every other place `w`. -/
theorem exists_sub_tmul_mem_baseChange_and_forall_ne {N : Submodule R V}
    (hN : span K (N : Set V) = ⊤) (v : HeightOneSpectrum R)
    (y : v.adicCompletionIntegers K ⊗[R] V) :
    ∃ x : V,
      y - (1 : v.adicCompletionIntegers K) ⊗ₜ x ∈ N.baseChange (v.adicCompletionIntegers K) ∧
      ∀ w ≠ v,
        (1 : w.adicCompletionIntegers K) ⊗ₜ x ∈ N.baseChange (w.adicCompletionIntegers K) := by
  classical
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨x₁, hv₁, hw₁⟩ := h₁
    obtain ⟨x₂, hv₂, hw₂⟩ := h₂
    refine ⟨x₁ + x₂, ?_, fun w hw ↦ ?_⟩
    · rw [tmul_add, add_sub_add_comm]
      exact add_mem hv₁ hv₂
    · rw [tmul_add]
      exact add_mem (hw₁ w hw) (hw₂ w hw)
  | tmul o x₀ =>
    -- Clear the denominator of `x₀` with `c`, and approximate `o` modulo `c` at `v` by an element
    -- `r` of `R` that is divisible by `c` at every other place.
    obtain ⟨c, hc, hcx⟩ := IsLattice.exists_ne_zero_smul_mem K N hN x₀
    obtain ⟨r, hr⟩ := HeightOneSpectrum.exists_forall_sub_mem_span_singleton (K := K) hc
      (Pi.single v o)
    -- An element of `c 𝒪_w` tensored with `x₀` lies in the completion of `N` at `w`.
    have key (w : HeightOneSpectrum R) {s : w.adicCompletionIntegers K}
        (hs : s ∈ Ideal.span {algebraMap R (w.adicCompletionIntegers K) c}) :
        s ⊗ₜ x₀ ∈ N.baseChange (w.adicCompletionIntegers K) := by
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
      rw [mul_comm, ← Algebra.smul_def, smul_tmul]
      exact tmul_mem_baseChange_of_mem t hcx
    refine ⟨r • x₀, ?_, fun w hw ↦ ?_⟩
    · have := key v (neg_mem (hr v))
      rw [Pi.single_eq_same, neg_sub] at this
      rwa [← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← sub_tmul]
    · have := key w (hr w)
      rw [Pi.single_eq_of_ne hw, sub_zero] at this
      rwa [← smul_tmul, ← Algebra.algebraMap_eq_smul_one]

/-- **Lattice gluing.** If the gluing of the local submodules `L v` spans `V` over `K`, then its
completion at every height-one prime `v` is exactly `L v`. In particular this holds when some
`R`-submodule spanning `V` has all its completions inside the `L v`. -/
theorem baseChange_glueCompletions (hspan : span K (glueCompletions K L : Set V) = ⊤)
    (v : HeightOneSpectrum R) :
    (glueCompletions K L).baseChange (v.adicCompletionIntegers K) = L v := by
  refine (baseChange_glueCompletions_le v).antisymm fun y hy ↦ ?_
  obtain ⟨x, hxv, hxw⟩ := exists_sub_tmul_mem_baseChange_and_forall_ne hspan v y
  -- The approximating vector `x` lies in the gluing: at `v` it differs from `y ∈ L v` by an element
  -- of the completion of the gluing, and at every other place it lies in that completion.
  have hx : x ∈ glueCompletions K L := by
    refine mem_glueCompletions.2 fun w ↦ ?_
    by_cases hw : w = v
    · subst hw
      simpa using sub_mem hy (baseChange_glueCompletions_le w hxv)
    · exact baseChange_glueCompletions_le w (hxw w hw)
  have := add_mem hxv (tmul_mem_baseChange_of_mem (1 : v.adicCompletionIntegers K) hx)
  rwa [sub_add_cancel] at this

omit [Module K V] [IsScalarTower R K V] in
/-- Gluing the completions of a submodule gives back the submodule, since submodules are
determined by their completions. -/
@[simp]
theorem glueCompletions_baseChange (hR : ¬IsField R) (M : Submodule R V) :
    glueCompletions K (fun v ↦ M.baseChange (v.adicCompletionIntegers K)) = M := by
  refine le_antisymm (fun x hx ↦ ?_) (le_glueCompletions_iff.2 fun _ ↦ le_rfl)
  rw [← span_singleton_le_iff_mem, le_iff_forall_baseChange_adicCompletionIntegers_le K hR]
  intro v
  rw [baseChange_span, Set.image_singleton, span_le, Set.singleton_subset_iff]
  exact mem_glueCompletions.1 hx v

/-- **Uniqueness of the glued lattice.** If the gluing of the `L v` spans `V` over `K`, it is the
unique `R`-submodule of `V` whose completion at every `v` is `L v`. -/
theorem eq_glueCompletions_iff (hR : ¬IsField R)
    (hspan : span K (glueCompletions K L : Set V) = ⊤) {M : Submodule R V} :
    M = glueCompletions K L ↔
      ∀ v : HeightOneSpectrum R, M.baseChange (v.adicCompletionIntegers K) = L v := by
  rw [eq_iff_forall_baseChange_adicCompletionIntegers_eq K hR]
  simp only [baseChange_glueCompletions hspan]

end TauCeti
