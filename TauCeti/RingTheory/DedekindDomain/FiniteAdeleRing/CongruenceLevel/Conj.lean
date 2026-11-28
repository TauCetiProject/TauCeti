/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel.NhdsBasis

/-!
# Conjugates of principal congruence levels in `GL_n(𝔸_f)`

For a Dedekind domain `R` with fraction field `K` and a finite index type `ι`, write `K(N)` for
the principal congruence level `IsDedekindDomain.FiniteAdeleRing.principalLevel K ι N` of an ideal
`N` of `R` in `GL_n(𝔸_f) = GL_ι(𝔸_f)`. For `N ≠ ⊥` it is open
(`IsDedekindDomain.FiniteAdeleRing.isOpen_principalLevel`), and conjugation by a fixed element is
continuous, so the elements that conjugation by `g` carries into `K(N)` form a neighbourhood of
`1`. As the levels `K(M)`, `M ≠ ⊥`, form a basis of neighbourhoods of `1`
(`IsDedekindDomain.FiniteAdeleRing.hasBasis_nhds_one_principalLevel`), and finitely many
neighbourhoods of `1` meet in one, a single level `K(M)` has all of finitely many conjugates
`g_k⁻¹ K(M) g_k` inside given levels `K(N_k)`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.comap_conj_principalLevel_mem_nhds`: for `N ≠ ⊥`, the
  preimage of `K(N)` under conjugation by `g` is a neighbourhood of `1`.
* `IsDedekindDomain.FiniteAdeleRing.exists_forall_map_conj_principalLevel_le`: for finitely many
  `g_k` and nonzero `N_k` there is `M ≠ ⊥` with `g_k⁻¹ K(M) g_k ≤ K(N_k)` for every `k`.
* `IsDedekindDomain.FiniteAdeleRing.exists_map_conj_principalLevel_le`: the case of one element.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.Variety.exists_level_conj_mem`).
-/

public section

open Filter Topology

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- For `N ≠ ⊥`, the elements `x` of `GL_n(𝔸_f)` with `g x g⁻¹ ∈ K(N)` form a neighbourhood of
`1`: `K(N)` is open and conjugation by `g` is continuous. -/
theorem comap_conj_principalLevel_mem_nhds (g : GL ι 𝔸ᶠ[R, K]) {N : Ideal R} (hN : N ≠ ⊥) :
    ((principalLevel K ι N).comap (MulAut.conj g).toMonoidHom : Set (GL ι 𝔸ᶠ[R, K])) ∈ 𝓝 1 := by
  have hc : Continuous fun x : GL ι 𝔸ᶠ[R, K] ↦ g * x * g⁻¹ := by fun_prop
  refine ((isOpen_principalLevel K ι hN).preimage hc).mem_nhds ?_
  simpa only [Set.mem_preimage, mul_one, mul_inv_cancel, SetLike.mem_coe] using
    one_mem (principalLevel K ι N)

/-- **A common level for finitely many conjugates.** For finitely many `g_k ∈ GL_n(𝔸_f)` and
nonzero ideals `N_k` of `R`, there is a nonzero ideal `M` with `g_k⁻¹ K(M) g_k ≤ K(N_k)` for
every `k`. -/
theorem exists_forall_map_conj_principalLevel_le {κ : Type*} [Finite κ]
    (g : κ → GL ι 𝔸ᶠ[R, K]) {N : κ → Ideal R} (hN : ∀ k, N k ≠ ⊥) :
    ∃ M : Ideal R, M ≠ ⊥ ∧ ∀ k,
      (principalLevel K ι M).map (MulAut.conj (g k)⁻¹).toMonoidHom ≤
        principalLevel K ι (N k) := by
  obtain ⟨M, hM, hsub⟩ := (hasBasis_nhds_one_principalLevel K ι).mem_iff.1
    (iInter_mem.2 fun k ↦ comap_conj_principalLevel_mem_nhds K (g k)⁻¹ (hN k))
  exact ⟨M, hM, fun k ↦ Subgroup.map_le_iff_le_comap.2 fun x hx ↦ Set.mem_iInter.1 (hsub hx) k⟩

/-- **A level inside a conjugate level.** For `g ∈ GL_n(𝔸_f)` and a nonzero ideal `N` of `R`,
there is a nonzero ideal `M` with `g⁻¹ K(M) g ≤ K(N)`. -/
theorem exists_map_conj_principalLevel_le (g : GL ι 𝔸ᶠ[R, K]) {N : Ideal R} (hN : N ≠ ⊥) :
    ∃ M : Ideal R, M ≠ ⊥ ∧
      (principalLevel K ι M).map (MulAut.conj g⁻¹).toMonoidHom ≤ principalLevel K ι N := by
  obtain ⟨M, hM, h⟩ := exists_forall_map_conj_principalLevel_le K (fun _ : Unit ↦ g) fun _ ↦ hN
  exact ⟨M, hM, h ()⟩

end IsDedekindDomain.FiniteAdeleRing
