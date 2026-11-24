/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.ShortExact
public import TauCeti.LinearAlgebra.Prod

/-!
# Orientations of kernels at a breaking

Let `A : P → L × R` and `β : R → Q` be surjective linear maps of finite-dimensional vector spaces
over a linearly ordered field, and let `G = (id × β) ∘ A : P → L × Q`. The kernel of `G` contains
that of `A`, with quotient the kernel of `id × β`, which is the kernel `N` of `β` placed in the
second factor (`LinearMap.kerEquivKerIdProdMap`). Orientations of `ker A`, `L`, `N` and `Q`
therefore orient `P` in two ways, subspace first:

* through `0 → ker A → P → L × R → 0`, with `R` oriented by `0 → N → R → Q → 0`, the order is
  `[ker A][L][N][Q]`;
* through `0 → ker G → P → L × Q → 0`, with `ker G` oriented by `0 → ker A → ker G → N → 0`, the
  order is `[ker A][N][L][Q]`.

They differ by the sign `(-1) ^ (dim L · dim N)` of exchanging `L` and `N`
(`Orientation.shortExact_ker_prodMap_comp`).

**Broken trajectories.** This is the linear algebra of the orientations of spaces of Morse
trajectories near a broken trajectory. At a point `y` of a trajectory `u` from `p` to `r`, the
comparison map `A = (df_y, N_r) : V_p → ℝ × V_r`, which reads the derivative of `f` and the normal
coordinates of `W^s(r)` on the unstable directions `V_p` of `p`, is onto, its kernel is the tangent
space of the space `𝓜(p, r)` of trajectories, and `[V_p] = [ker A][ℝ][V_r]` orients `𝓜(p, r)`.
At a point of a trajectory `v` from `r` to `q` the comparison map `B = (B₁, B₂) : V_r → ℝ × V_q`
orients `𝓜(r, q)` in the same way. Trajectories from `p` to `q` close to the broken trajectory
`(u, v)` read the normal coordinates of `W^s(q)` through `V_r`, and their comparison maps are
expected to converge, up to positive rescaling of the second component, to
`G = (df_y, B₂ ∘ N_r) = (id × B₂) ∘ A`; that convergence belongs to the gluing analysis and is not
proved here. The orientation `[V_p] = [ker G][ℝ][V_q]` of the limiting tangent space is computed by
`Orientation.shortExact_ker_prodMap_comp_ker_prod` and
`Orientation.shortExactLeft_ker_prodMap_comp_ker_prod`: with `m₂ = dim ker B`, it is
`(-1) ^ (m₂ + 1)` times the orientation of `ker A` followed by that of `ker B₂`, which is
`[ker B]` followed by a vector `w₀` with `B w₀ = (1, 0)`. In particular, when
`ind p = ind r + 1 = ind q + 2`, the maps `A` and `B` are isomorphisms, the orientations of their
zero kernels are the signs `ε(u)` and `ε(v)` of the two trajectories, and the line `ker G` is
oriented by `-ε(u) ε(v)` times the gluing direction `g`, the vector with `A g = (0, w₀)`.
Comparing the gluing direction with the outward direction of the compactified space of
trajectories then gives the boundary orientation of the broken end.

## Main results

* `Orientation.prod_shortExact_eq_shortExact_ker_prodMap`: `[L][N][Q]` is `(-1) ^ (dim L · dim N)`
  times `[N][L][Q]` as orientations of `L × R`.
* `Orientation.shortExact_ker_prodMap_comp`: the orientations of `P` through `ker A` and through
  `ker ((id × β) ∘ A)` differ by `(-1) ^ (dim L · dim N)`.
* `Orientation.shortExact_ker_prodMap_comp_ker_prod`: the case of two comparison maps
  `A : P → K × R` and `(B₁, B₂) : R → K × Q`, where the sign is `(-1) ^ (dim ker (B₁, B₂) + 1)`.
* `Orientation.shortExactLeft_ker_prodMap_comp_ker_prod`: the same statement for the orientations
  of the kernels induced from orientations of `P`, `R` and `Q`, as the orientations of spaces of
  trajectories are defined.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 2.3 (orientations of the spaces of trajectories and
  the boundary of the compactified space of index-two trajectories).
-/

public section
noncomputable section

open Module LinearMap

namespace Orientation

variable {K P L R Q : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup P] [Module K P] [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K P] [FiniteDimensional K L]
  [FiniteDimensional K R] [FiniteDimensional K Q]

/-! ### Exchanging a factor with a kernel -/

section Exchange

variable {β : R →ₗ[K] Q} {l ν c : ℕ}

/-- Let `β : R → Q` be onto with kernel `N`. Orient `R` from `N` and `Q`, subspace first, and
`L × R` as the product `[L][R] = [L][N][Q]`. Then `L × R` is `(-1) ^ (dim L · dim N)` times the
orientation `[N][L][Q]` of the short exact sequence `0 → N → L × R → L × Q → 0`, with `N` placed in
the second factor and the quotient map `id × β`. -/
theorem prod_shortExact_eq_shortExact_ker_prodMap (hβ : Function.Surjective β)
    (oL : Orientation K L (Fin l)) (n : Orientation K (ker β) (Fin ν))
    (q : Orientation K Q (Fin c)) (hl : finrank K L = l) (hν : finrank K (ker β) = ν)
    (hc : finrank K Q = c) (hR : finrank K R = ν + c) :
    prod oL (shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map β) hβ n q hν hc)
        hl hR =
      (-1 : Kˣ) ^ (l * ν) • reindex K (L × R) (finCongr (by omega))
        (shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map _)
          (surjective_prodMap Function.surjective_id hβ) (map (Fin ν) (kerEquivKerIdProdMap L β) n)
          (prod oL q hl hc) ((kerEquivKerIdProdMap L β).finrank_eq.symm.trans hν)
          (by rw [finrank_prod, hl, hc])) := by
  -- `[L][R] = [L × N][Q]` with `[L × N] = [L][N]`.
  have A := shortExact_id_prodMap (Submodule.injective_subtype _) (exact_subtype_ker_map β) hβ
    oL n q hl hν hc
  -- `[L][N] = (-1) ^ (l ν) [N][L]`, and `[N][L]` is the subspace-first orientation of
  -- `0 → N → L × N → L → 0`.
  have B := map_prodComm_prod n oL hν hl
  have C := map_shortExact inl_injective (Function.Exact.inl_snd (R := K) (M := ker β) (N := L))
    snd_surjective hν hl inr_injective (Function.Exact.inr_fst (R := K) (M := L) (N := ker β))
    fst_surjective (LinearEquiv.refl K (ker β)) (LinearEquiv.prodComm K (ker β) L)
    (LinearEquiv.refl K L) (by ext <;> simp) (by ext <;> simp) n oL
  simp only [map_refl, Equiv.refl_apply, shortExact_inl_snd] at C
  rw [C] at B
  -- Collapse the tower `N ⊆ L × N ⊆ L × R` with quotients `L` and `Q`.
  have D := shortExact_shortExact inr_injective
    (Function.Exact.inr_fst (R := K) (M := L) (N := ker β)) fst_surjective
    (injective_prodMap Function.injective_id (Submodule.injective_subtype _))
    ((exact_subtype_ker_map β).id_prodMap_comp_snd (Z := L))
    (surjective_comp hβ snd_surjective) (h := fst K L R) (by ext <;> simp) n oL q hν hl hc
    (by rw [finrank_prod, hl, hν]; omega)
  -- Identify the collapsed sequence with `0 → ker (id × β) → L × R → L × Q → 0`.
  have hex : Function.Exact ((LinearMap.id : L →ₗ[K] L).prodMap (ker β).subtype)
      (β ∘ₗ snd K L R) := (exact_subtype_ker_map β).id_prodMap_comp_snd
  have hinj : Function.Injective
      ((LinearMap.id : L →ₗ[K] L).prodMap (ker β).subtype ∘ₗ inr K L (ker β)) :=
    injective_comp (injective_prodMap Function.injective_id (Submodule.injective_subtype _))
      inr_injective
  have hex' := (Function.Exact.inr_fst (R := K) (M := L) (N := ker β)).comp_prod hex
    (h := fst K L R) (by ext <;> simp)
  have hsurj : Function.Surjective ((fst K L R).prod (β ∘ₗ snd K L R)) :=
    surjective_prod_of_comp_eq_zero hex.linearMap_comp_eq_zero (fun x ↦ ⟨(x, 0), by simp⟩)
      (surjective_comp hβ snd_surjective)
  have E := map_shortExact hinj hex' hsurj hν (by rw [finrank_prod, hl, hc])
    (Submodule.injective_subtype _) (exact_subtype_ker_map _)
    (surjective_prodMap Function.surjective_id hβ) (kerEquivKerIdProdMap L β) (LinearEquiv.refl K _)
    (LinearEquiv.refl K _) (by ext <;> simp) (by ext <;> simp) n (prod oL q hl hc)
  simp only [map_refl, Equiv.refl_apply] at E
  -- Combine: `[L][R] = [L][N][Q] = (-1) ^ (l ν) [N][L][Q]`.
  have A' := (Equiv.eq_symm_apply _).2 A.symm
  have B' : oL.prod n hl hν = (-1 : Kˣ) ^ (ν * l) •
      reindex K (L × ker β) (finCongr (add_comm ν l))
        (shortExact inr_injective (Function.Exact.inr_fst (R := K) (M := L) (N := ker β))
          fst_surjective n oL hν hl) := by
    simp [B, smul_smul, ← mul_pow, reindex_finCongr_reindex_finCongr]
  rw [A', reindex_symm, finCongr_symm, B', shortExact_units_smul_left,
    shortExact_reindex_finCongr_left, D, E]
  simp only [reindex_units_smul, reindex_finCongr_reindex_finCongr, mul_comm l ν]

end Exchange

/-! ### The kernel of `(id × β) ∘ A` -/

section Comparison

variable {A : P →ₗ[K] L × R} {β : R →ₗ[K] Q} {m l ν c : ℕ}

/-- **Orienting the kernel of `(id × β) ∘ A`.** Let `A : P → L × R` and `β : R → Q` be onto, and
`G = (id × β) ∘ A`. Orient `ker G` from `ker A` and `ker (id × β)`, the kernel `N` of `β` placed in
the second factor, through `0 → ker A → ker G → ker (id × β) → 0`. Then `P` oriented from `ker G`
and `[L][Q]` is `(-1) ^ (dim L · dim N)` times `P` oriented from `ker A` and `[L][R]`, where `R` is
oriented from `N` and `Q`: the two orders `[ker A][N][L][Q]` and `[ker A][L][N][Q]` differ by the
exchange of `L` and `N`. -/
theorem shortExact_ker_prodMap_comp (hA : Function.Surjective A) (hβ : Function.Surjective β)
    (o : Orientation K (ker A) (Fin m)) (oL : Orientation K L (Fin l))
    (n : Orientation K (ker β) (Fin ν)) (q : Orientation K Q (Fin c))
    (hm : finrank K (ker A) = m) (hl : finrank K L = l) (hν : finrank K (ker β) = ν)
    (hc : finrank K Q = c) (hR : finrank K R = ν + c) :
    shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map _)
        (surjective_comp (surjective_prodMap Function.surjective_id hβ) hA)
        (shortExact (Submodule.inclusion_injective (ker_le_ker_comp A (id.prodMap β)))
          (exact_inclusion_kerCompToKer A _) (surjective_kerCompToKer A _ hA) o
          (map (Fin ν) (kerEquivKerIdProdMap L β) n) hm
          ((kerEquivKerIdProdMap L β).finrank_eq.symm.trans hν))
        (prod oL q hl hc)
        (by
          rw [finrank_ker_comp_of_surjective _ hA, ← (kerEquivKerIdProdMap L β).finrank_eq, hm, hν])
        (by rw [finrank_prod, hl, hc]) =
      (-1 : Kˣ) ^ (l * ν) • reindex K P (finCongr (by omega))
        (shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map A) hA o
          (prod oL (shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map β) hβ n q
            hν hc) hl hR) hm (by rw [finrank_prod, hl, hR])) := by
  have hG : finrank K (ker (id.prodMap β ∘ₗ A)) = m + ν := by
    rw [finrank_ker_comp_of_surjective _ hA, ← (kerEquivKerIdProdMap L β).finrank_eq, hm, hν]
  -- Write `[L][R]` as `(-1) ^ (l ν) [N][L][Q]`, then pass the tower `ker A ⊆ ker G ⊆ P` through
  -- the quotient.
  rw [prod_shortExact_eq_shortExact_ker_prodMap hβ oL n q hl hν hc hR,
    shortExact_units_smul_right, shortExact_reindex_finCongr_right,
    shortExact_shortExact_right (Submodule.injective_subtype _) (exact_subtype_ker_map A) hA
      (Submodule.injective_subtype _) (exact_subtype_ker_map _)
      (surjective_prodMap Function.surjective_id hβ)
      (Submodule.inclusion_injective (ker_le_ker_comp A (id.prodMap β)))
      (exact_inclusion_kerCompToKer A _) (surjective_kerCompToKer A _ hA)
      (Submodule.injective_subtype _) (exact_subtype_ker_map _)
      (surjective_comp (surjective_prodMap Function.surjective_id hβ) hA)
      (Submodule.subtype_comp_inclusion _ _ _)
      (by ext <;> simp) rfl _ _ _ hm _ _ _ hG]
  simp [reindex_finCongr_reindex_finCongr, smul_smul, ← mul_pow]

end Comparison

/-! ### Two comparison maps -/

section Broken

variable {A : P →ₗ[K] K × R} {B₁ : R →ₗ[K] K} {B₂ : R →ₗ[K] Q} {m₁ m₂ c : ℕ}

/-- **The orientation at a broken trajectory.** Let `A : P → K × R` and
`B = (B₁, B₂) : R → K × Q` be onto, oriented kernels `ker A` and `ker B`, and `Q` oriented. Orient
`R` as `[ker B][K][Q]` and `P` as `[ker A][K][R]`, subspace first. The kernel of
`G = (id × B₂) ∘ A` is oriented from `ker A` and `ker (id × B₂)`, which is `ker B₂` placed in the
second factor, oriented as `[ker B][K]` through `0 → ker B → ker B₂ → K → 0` with the quotient
map `B₁`. Then `P` oriented as `[ker G][K][Q]` is `(-1) ^ (dim ker B + 1)` times `[ker A][K][R]`.

For comparison maps of Morse trajectories, `ker A`, `ker B` and `ker G` are the tangent spaces of
the spaces of trajectories from `p` to `r`, from `r` to `q`, and, in the limit along trajectories
breaking at `r`, from `p` to `q`. The line in `ker B₂` lifting `K`, spanned by `w₀` with
`B w₀ = (1, 0)`, is the image under `A` of the gluing direction `g ∈ ker G`, the vector with
`A g = (0, w₀)`. -/
theorem shortExact_ker_prodMap_comp_ker_prod (hA : Function.Surjective A)
    (hB : Function.Surjective (B₁.prod B₂)) (o₁ : Orientation K (ker A) (Fin m₁))
    (o₂ : Orientation K (ker (B₁.prod B₂)) (Fin m₂)) (oq : Orientation K Q (Fin c))
    (hm₁ : finrank K (ker A) = m₁) (hm₂ : finrank K (ker (B₁.prod B₂)) = m₂)
    (hc : finrank K Q = c) (hR : finrank K R = m₂ + (1 + c)) :
    shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map _)
        (surjective_comp (surjective_prodMap Function.surjective_id
          (surjective_of_surjective_prod_right hB)) hA)
        (shortExact (Submodule.inclusion_injective (ker_le_ker_comp A (id.prodMap B₂)))
          (exact_inclusion_kerCompToKer A _) (surjective_kerCompToKer A _ hA) o₁
          (map (Fin (m₂ + 1)) (kerEquivKerIdProdMap K B₂)
            (shortExact (Submodule.inclusion_injective ((ker_prod B₁ B₂).trans_le inf_le_right))
              (exact_inclusion_ker_prod B₁ B₂) (surjective_comp_subtype_ker hB) o₂
              (Basis.singleton (Fin 1) K).orientation hm₂ (finrank_self K))) hm₁
          ((kerEquivKerIdProdMap K B₂).finrank_eq.symm.trans (by
            rw [finrank_ker_eq_of_surjective_prod hB, hm₂, finrank_self])))
        ((Basis.singleton (Fin 1) K).orientation.prod oq (finrank_self K) hc)
        (by
          rw [finrank_ker_comp_of_surjective _ hA, ← (kerEquivKerIdProdMap K B₂).finrank_eq,
            finrank_ker_eq_of_surjective_prod hB, hm₁, hm₂, finrank_self])
        (by rw [finrank_prod, finrank_self, hc]) =
      (-1 : Kˣ) ^ (m₂ + 1) • reindex K P (finCongr (by omega))
        (shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map A) hA o₁
          ((Basis.singleton (Fin 1) K).orientation.prod
            (shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map _) hB o₂
              ((Basis.singleton (Fin 1) K).orientation.prod oq (finrank_self K) hc) hm₂
              (by rw [finrank_prod, finrank_self, hc])) (finrank_self K)
            (hR.trans (by omega))) hm₁ (by rw [finrank_prod, finrank_self, hR])) := by
  have hB₂ : Function.Surjective B₂ := surjective_of_surjective_prod_right hB
  have hν : finrank K (ker B₂) = m₂ + 1 := by
    rw [finrank_ker_eq_of_surjective_prod hB, hm₂, finrank_self]
  set n := shortExact (Submodule.inclusion_injective ((ker_prod B₁ B₂).trans_le inf_le_right))
    (exact_inclusion_ker_prod B₁ B₂) (surjective_comp_subtype_ker hB) o₂
    (Basis.singleton (Fin 1) K).orientation hm₂ (finrank_self K)
  -- `R` oriented from `ker B` and `K × Q` is `R` oriented from `ker B₂` and `Q`, once `ker B₂` is
  -- oriented from `ker B` and `K`.
  have T := shortExact_shortExact
    (Submodule.inclusion_injective ((ker_prod B₁ B₂).trans_le inf_le_right))
    (exact_inclusion_ker_prod B₁ B₂) (surjective_comp_subtype_ker hB)
    (Submodule.injective_subtype _) (exact_subtype_ker_map B₂) hB₂ (h := B₁) rfl o₂
    (Basis.singleton (Fin 1) K).orientation oq hm₂ (finrank_self K) hc hν
  have T' := map_shortExact (injective_comp (Submodule.injective_subtype _)
      (Submodule.inclusion_injective ((ker_prod B₁ B₂).trans_le inf_le_right)))
    ((exact_inclusion_ker_prod B₁ B₂).comp_prod (exact_subtype_ker_map B₂) rfl)
    (surjective_prod_of_comp_eq_zero (exact_subtype_ker_map B₂).linearMap_comp_eq_zero
      (surjective_comp_subtype_ker hB) hB₂) hm₂ (by rw [finrank_prod, finrank_self, hc])
    (Submodule.injective_subtype _) (exact_subtype_ker_map _) hB (LinearEquiv.refl K _)
    (LinearEquiv.refl K _) (LinearEquiv.refl K _)
    (by ext; simp) (by ext <;> simp) o₂
    ((Basis.singleton (Fin 1) K).orientation.prod oq (finrank_self K) hc)
  simp only [map_refl, Equiv.refl_apply] at T'
  rw [shortExact_ker_prodMap_comp hA hB₂ o₁ _ n oq hm₁ (finrank_self K) hν hc (by omega), T,
    T', prod_reindex_finCongr_right, shortExact_reindex_finCongr_right]
  simp only [reindex_finCongr_reindex_finCongr, one_mul]

/-- **The orientation at a broken trajectory**, for the orientations of the kernels induced from
orientations `op` of `P`, `or` of `R` and `oq` of `Q`. Orient `ker A` by `[P] = [ker A][K][R]`,
`ker B` by `[R] = [ker B][K][Q]` and `ker G` by `[P] = [ker G][K][Q]`, for
`G = (id × B₂) ∘ A`. Then the orientation of `ker G` is `(-1) ^ (dim ker B + 1)` times the one
built from `ker A` and `ker (id × B₂)`, which is `ker B₂` in the second factor oriented as
`[ker B][K]`. -/
theorem shortExactLeft_ker_prodMap_comp_ker_prod (hA : Function.Surjective A)
    (hB : Function.Surjective (B₁.prod B₂)) (op : Orientation K P (Fin (m₁ + (1 + (m₂ + (1 + c))))))
    (or : Orientation K R (Fin (m₂ + (1 + c)))) (oq : Orientation K Q (Fin c))
    (hm₁ : finrank K (ker A) = m₁) (hm₂ : finrank K (ker (B₁.prod B₂)) = m₂)
    (hc : finrank K Q = c) (hR : finrank K R = m₂ + (1 + c)) :
    shortExactLeft (Submodule.injective_subtype _) (exact_subtype_ker_map _)
        (surjective_comp (surjective_prodMap Function.surjective_id
          (surjective_of_surjective_prod_right hB)) hA)
        (by
          rw [finrank_ker_comp_of_surjective _ hA, ← (kerEquivKerIdProdMap K B₂).finrank_eq,
            finrank_ker_eq_of_surjective_prod hB, hm₁, hm₂, finrank_self])
        (by rw [finrank_prod, finrank_self, hc])
        (reindex K P (finCongr (by omega)) op)
        ((Basis.singleton (Fin 1) K).orientation.prod oq (finrank_self K) hc) =
      (-1 : Kˣ) ^ (m₂ + 1) •
        shortExact (Submodule.inclusion_injective (ker_le_ker_comp A (id.prodMap B₂)))
          (exact_inclusion_kerCompToKer A _) (surjective_kerCompToKer A _ hA)
          (shortExactLeft (Submodule.injective_subtype _) (exact_subtype_ker_map A) hA hm₁
            (by rw [finrank_prod, finrank_self, hR]) op
            ((Basis.singleton (Fin 1) K).orientation.prod or (finrank_self K) hR))
          (map (Fin (m₂ + 1)) (kerEquivKerIdProdMap K B₂)
            (shortExact (Submodule.inclusion_injective ((ker_prod B₁ B₂).trans_le inf_le_right))
              (exact_inclusion_ker_prod B₁ B₂) (surjective_comp_subtype_ker hB)
              (shortExactLeft (Submodule.injective_subtype _) (exact_subtype_ker_map _) hB hm₂
                (by rw [finrank_prod, finrank_self, hc]) or
                ((Basis.singleton (Fin 1) K).orientation.prod oq (finrank_self K) hc))
              (Basis.singleton (Fin 1) K).orientation hm₂ (finrank_self K))) hm₁
          ((kerEquivKerIdProdMap K B₂).finrank_eq.symm.trans (by
            rw [finrank_ker_eq_of_surjective_prod hB, hm₂, finrank_self])) := by
  rw [shortExactLeft_eq_iff, shortExact_units_smul_left,
    shortExact_ker_prodMap_comp_ker_prod hA hB _ _ oq hm₁ hm₂ hc hR, shortExact_shortExactLeft,
    shortExact_shortExactLeft]
  simp [smul_smul, ← mul_pow]

end Broken

end Orientation
