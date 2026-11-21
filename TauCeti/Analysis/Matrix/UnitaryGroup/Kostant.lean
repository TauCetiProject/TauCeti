/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Unitary
public import TauCeti.Analysis.Matrix.UnitaryGroup.SchurHorn
public import TauCeti.Analysis.Matrix.UnitaryGroup.Weyl
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Kostant's convexity theorem for the coadjoint orbits of `U(n)`

Let `T ⊆ U(n)` be the diagonal torus (`TauCeti.unitaryTorus`). Its Lie algebra `𝔱 ⊆ 𝔲(n)` consists
of the diagonal skew-Hermitian matrices `i diag(θ)`, `θ ∈ ℝⁿ`
(`TauCeti.unitaryTorusLieMap`, `TauCeti.mem_range_unitaryTorusLieMap_iff`). We use these angular
coordinates `θ`, for which `θ ↦ diag(e^(i θ₁), …, e^(i θₙ))` parametrizes `T` with period `2π` in
each coordinate. Restriction of covectors from `𝔲(n)` to `𝔱`, read in these coordinates, is the
linear map `pr_𝔱* : 𝔲(n)* → ℝⁿ`, `(pr_𝔱* ν)ₖ = ν (i Eₖₖ)` (`TauCeti.unitaryTorusRestriction`), so
that `ν (i diag(θ)) = ∑ₖ θₖ (pr_𝔱* ν)ₖ` (`TauCeti.apply_unitaryTorusLieMap`). Since the inclusion of
a coadjoint orbit into `𝔲(n)*` is the moment map of the coadjoint action, its composite with
`pr_𝔱*` is the moment map of the action of `T` on the orbit.

Under the trace pairing `⟨H, X⟩ = -i tr(H X)` of `TauCeti.Algebra.Lie.Unitary`, which identifies
`𝔲(n)*` with the Hermitian matrices, the restriction to the torus is the **diagonal**:
`pr_𝔱* ⟨H, ·⟩ = (H₁₁, …, Hₙₙ)` (`TauCeti.unitaryTorusRestriction_unitaryTracePairing`). Since the
coadjoint action is unitary conjugation, the image of the coadjoint orbit through `⟨H, ·⟩` under the
torus moment map is the set of diagonals of the matrices `U H Uᴴ`, which the Schur–Horn theorem
(`Matrix.IsHermitian.range_re_diag_unitary_mul_mul_star`) identifies with the permutohedron of the
eigenvalues of `H` (`TauCeti.range_unitaryTorusRestriction_unitaryCoadjointRepresentation`).

This is **Kostant's convexity theorem** for `K = U(n)`. The covectors on `𝔲(n)` fixed by the torus
are exactly the `⟨diag(s), ·⟩` for real `s` (`TauCeti.mem_range_unitaryTorusDualInclusion_iff`),
and `pr_𝔱*` is a left inverse of `s ↦ ⟨diag(s), ·⟩`
(`TauCeti.unitaryTorusRestriction_unitaryTorusDualInclusion`): this is the embedding of `𝔱*` into
`𝔲(n)*` as the torus-fixed covectors (`TauCeti.unitaryTorusDualInclusion`). The Weyl group
`N(T) / T` is the symmetric group (`TauCeti.Analysis.Matrix.UnitaryGroup.Weyl`), and for
`ν = ⟨diag(s), ·⟩` the torus restrictions of its translates by the normalizer `N(T)` are exactly
the rearrangements of `s` (`TauCeti.unitaryTorusRestriction_image_normalizer_unitaryTorus`). So
for `ν ∈ 𝔱*`

`pr_𝔱* (K · ν) = conv (W · ν)`

(`TauCeti.range_unitaryTorusRestriction_unitaryCoadjointRepresentation_unitaryTorusDualInclusion`
and, with the normalizer itself,
`TauCeti.range_unitaryTorusRestriction_eq_convexHull_image_normalizer`). Repeated entries of `s` are
allowed: they give smaller orbits with the same description. The statements about the normalizer
are made for the index type `Fin n`, on which the Weyl group of `U(n)` is computed.

## Main definitions

* `TauCeti.unitaryTorusLieMap ι`: the map `θ ↦ i diag(θ)` onto the Lie algebra of the diagonal
  torus.
* `TauCeti.unitaryTorusRestriction ι`: the restriction `pr_𝔱* : 𝔲(n)* → ℝⁿ` of covectors to the
  Lie algebra of the diagonal torus, in the coordinates `θ`.
* `TauCeti.unitaryTorusDualInclusion ι`: the inclusion `s ↦ ⟨diag(s), ·⟩` of `𝔱*` into `𝔲(n)*`.

## Main results

* `TauCeti.unitaryTorusRestriction_unitaryTracePairing`: the torus restriction of `⟨H, ·⟩` is the
  diagonal of `H`.
* `TauCeti.range_unitaryTorusRestriction_unitaryCoadjointRepresentation`: the torus moment image of
  the coadjoint orbit through `⟨H, ·⟩` is the permutohedron of the eigenvalues of `H`.
* `TauCeti.mem_range_unitaryTorusDualInclusion_iff`: the torus-fixed covectors are `𝔱*`.
* `TauCeti.unitaryTorusRestriction_image_normalizer_unitaryTorus`: the Weyl orbit of `s ∈ 𝔱*` is
  the set of rearrangements of `s`.
* `TauCeti.range_unitaryTorusRestriction_eq_convexHull_image_normalizer`: Kostant's theorem
  `pr_𝔱* (K · ν) = conv (pr_𝔱* (N(T) · ν))` for `ν ∈ 𝔱*`.

## References

* B. Kostant, *On convexity, the Weyl group and the Iwasawa decomposition*, Ann. Sci. École Norm.
  Sup. (4) **6** (1973), 413–455, Theorem 8.2 (the linear convexity theorem).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. **14** (1982),
  1–15, §1 (the Schur–Horn theorem as the convexity theorem for `U(n)`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer (2001), §27.
-/

public section

noncomputable section

open Matrix Module Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Lie algebra of the diagonal torus -/

/-- `i diag(θ)` is skew-Hermitian. -/
theorem diagonal_I_mul_mem_unitaryLieAlgebra (θ : ι → ℝ) :
    diagonal (fun k => I * θ k) ∈ unitaryLieAlgebra ι := by
  rw [mem_unitaryLieAlgebra_iff, diagonal_conjTranspose, diagonal_neg]
  congr 1
  ext k
  simp

variable (ι) in
/-- The map `θ ↦ i diag(θ)` from `ℝⁿ` onto the Lie algebra `𝔱` of the diagonal torus of `U(n)`,
the diagonal skew-Hermitian matrices (`TauCeti.mem_range_unitaryTorusLieMap_iff`). -/
def unitaryTorusLieMap : (ι → ℝ) →ₗ[ℝ] unitaryLieAlgebra ι where
  toFun θ := ⟨diagonal (fun k => I * θ k), diagonal_I_mul_mem_unitaryLieAlgebra θ⟩
  map_add' θ θ' := Subtype.ext (by simp [mul_add])
  map_smul' c θ := Subtype.ext (by
    ext i j
    by_cases h : i = j <;> simp [h, Complex.real_smul, mul_left_comm])

@[simp]
theorem coe_unitaryTorusLieMap_apply (θ : ι → ℝ) :
    (unitaryTorusLieMap ι θ : Matrix ι ι ℂ) = diagonal fun k => I * θ k :=
  (rfl)

/-- **The Lie algebra of the diagonal torus is the diagonal part of `𝔲(n)`**: an element of `𝔲(n)`
is of the form `i diag(θ)` exactly when it is a diagonal matrix. -/
theorem mem_range_unitaryTorusLieMap_iff {X : unitaryLieAlgebra ι} :
    X ∈ LinearMap.range (unitaryTorusLieMap ι) ↔ (X : Matrix ι ι ℂ).IsDiag := by
  refine ⟨fun ⟨θ, hθ⟩ => hθ ▸ isDiag_diagonal _, fun hX => ⟨fun k => ((X : Matrix ι ι ℂ) k k).im,
    Subtype.ext ?_⟩⟩
  -- The diagonal entries of a skew-Hermitian matrix are purely imaginary.
  have hre (k : ι) : ((X : Matrix ι ι ℂ) k k).re = 0 := by
    have h := congrArg re (congrFun₂ (conjTranspose_coe_unitaryLieAlgebra X) k k)
    rw [conjTranspose_apply, Matrix.neg_apply, star_def, conj_re, neg_re] at h
    linarith
  rw [coe_unitaryTorusLieMap_apply, ← hX.diagonal_diag]
  congr 1
  ext k
  apply Complex.ext <;> simp [hre k]

/-! ### Restriction of covectors to the torus -/

variable (ι) in
/-- The **restriction of covectors to the Lie algebra of the diagonal torus**, read in the
coordinates `θ` of `i diag(θ)`: `(pr_𝔱* ν)ₖ = ν (i Eₖₖ)`, so that
`ν (i diag(θ)) = ∑ₖ θₖ (pr_𝔱* ν)ₖ` (`TauCeti.apply_unitaryTorusLieMap`). On a coadjoint orbit it is
the moment map of the action of the diagonal torus. -/
def unitaryTorusRestriction : Dual ℝ (unitaryLieAlgebra ι) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun k => LinearMap.applyₗ (unitaryTorusLieMap ι (Pi.single k 1))

theorem unitaryTorusRestriction_apply (ν : Dual ℝ (unitaryLieAlgebra ι)) (k : ι) :
    unitaryTorusRestriction ι ν k = ν (unitaryTorusLieMap ι (Pi.single k 1)) :=
  (rfl)

/-- `pr_𝔱* ν` is the covector `θ ↦ ν (i diag(θ))` on `𝔱` in the coordinates `θ`:
`ν (i diag(θ)) = ∑ₖ θₖ (pr_𝔱* ν)ₖ`. -/
theorem apply_unitaryTorusLieMap (ν : Dual ℝ (unitaryLieAlgebra ι)) (θ : ι → ℝ) :
    ν (unitaryTorusLieMap ι θ) = ∑ k, θ k * unitaryTorusRestriction ι ν k := by
  conv_lhs => rw [← Finset.univ_sum_single θ]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show Pi.single k (θ k) = θ k • Pi.single k (1 : ℝ) by
      rw [← Pi.single_smul, smul_eq_mul, mul_one],
    map_smul, map_smul, smul_eq_mul, unitaryTorusRestriction_apply]

/-- **The torus restriction of `⟨H, ·⟩` is the diagonal of `H`**: under the trace pairing
`⟨H, X⟩ = -i tr(H X)`, the moment map of the diagonal torus reads off the diagonal entries. -/
@[simp]
theorem unitaryTorusRestriction_unitaryTracePairing (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    unitaryTorusRestriction ι (unitaryTracePairing ι H) = fun k => ((H : Matrix ι ι ℂ) k k).re := by
  ext k
  have h := ofReal_unitaryTracePairing_apply H (unitaryTorusLieMap ι (Pi.single k 1))
  rw [coe_unitaryTorusLieMap_apply, neg_I_mul_trace_mul_diagonal_I_mul] at h
  rw [unitaryTorusRestriction_apply, ← ofReal_re (unitaryTracePairing ι H _), h]
  simp [Pi.single_apply]

/-! ### The torus-fixed covectors -/

variable (ι) in
/-- The **inclusion `𝔱* → 𝔲(n)*`** sending `s` to the covector `⟨diag(s), ·⟩` of the real diagonal
matrix `diag(s)`. Its image is the set of covectors fixed by the diagonal torus
(`TauCeti.mem_range_unitaryTorusDualInclusion_iff`), and the torus restriction is a left inverse
(`TauCeti.unitaryTorusRestriction_unitaryTorusDualInclusion`). -/
def unitaryTorusDualInclusion : (ι → ℝ) →ₗ[ℝ] Dual ℝ (unitaryLieAlgebra ι) where
  toFun s := unitaryTracePairing ι ⟨diagonal fun k => (s k : ℂ),
    (isHermitian_diagonal_iff.mpr fun k => conj_ofReal (s k)).isSelfAdjoint⟩
  map_add' s s' := by
    rw [← map_add]
    congr 1
    exact Subtype.ext (by simp)
  map_smul' c s := by
    rw [← map_smul]
    congr 1
    exact Subtype.ext (by ext i j; by_cases h : i = j <;> simp [h])

theorem unitaryTorusDualInclusion_apply (s : ι → ℝ) :
    unitaryTorusDualInclusion ι s =
      unitaryTracePairing ι ⟨diagonal fun k => (s k : ℂ),
        (isHermitian_diagonal_iff.mpr fun k => conj_ofReal (s k)).isSelfAdjoint⟩ :=
  (rfl)

/-- **The torus restriction is a left inverse of the inclusion of `𝔱*`**: the restriction of
`⟨diag(s), ·⟩` to the Lie algebra of the diagonal torus is `s`. -/
@[simp]
theorem unitaryTorusRestriction_unitaryTorusDualInclusion (s : ι → ℝ) :
    unitaryTorusRestriction ι (unitaryTorusDualInclusion ι s) = s := by
  rw [unitaryTorusDualInclusion_apply, unitaryTorusRestriction_unitaryTracePairing]
  ext k
  simp

/-- **The covectors fixed by the diagonal torus are `𝔱*`**: a covector on `𝔲(n)` is fixed by the
coadjoint action of every element of the diagonal torus exactly when it is `⟨diag(s), ·⟩` for a
real tuple `s`. -/
theorem mem_range_unitaryTorusDualInclusion_iff {ν : Dual ℝ (unitaryLieAlgebra ι)} :
    ν ∈ LinearMap.range (unitaryTorusDualInclusion ι) ↔
      ∀ t ∈ unitaryTorus ι, unitaryCoadjointRepresentation ι t ν = ν := by
  constructor
  · rintro ⟨s, rfl⟩ t ht
    obtain ⟨z, rfl⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp ht
    rw [unitaryTorusDualInclusion_apply, ← Representation.mem_stabilizer,
      mem_stabilizer_unitaryCoadjointRepresentation_unitaryTracePairing_iff]
    simp only [coe_unitaryTorusHom, diagonal_mul_diagonal, mul_comm]
  · intro h
    obtain ⟨H, rfl⟩ := (unitaryTracePairingEquiv ι).surjective ν
    rw [unitaryTracePairingEquiv_apply] at h ⊢
    have hH : (H : Matrix ι ι ℂ).IsHermitian := (H.property : IsSelfAdjoint
        (H : Matrix ι ι ℂ)).isHermitian
    have hdiag : (H : Matrix ι ι ℂ).IsDiag := isDiag_of_forall_commute_unitaryTorusHom fun z =>
      mem_stabilizer_unitaryCoadjointRepresentation_unitaryTracePairing_iff.mp
        (Representation.mem_stabilizer.mpr (h _ (unitaryTorusHom_mem_unitaryTorus z)))
    refine ⟨fun k => ((H : Matrix ι ι ℂ) k k).re, ?_⟩
    rw [unitaryTorusDualInclusion_apply]
    congr 1
    -- The diagonal entries of a Hermitian matrix are real.
    exact Subtype.ext <| (congrArg diagonal (funext hH.coe_re_apply_self)).trans hdiag.diagonal_diag

/-- **The torus moment map on a coadjoint orbit through `𝔱*`**: the restriction to the torus of
`Ad*_U ⟨diag(s), ·⟩` is the tuple of averages `∑ᵢ |Uₖᵢ|² sᵢ` of `s`, with the doubly stochastic
weights `|Uₖᵢ|²`. -/
theorem unitaryTorusRestriction_unitaryCoadjointRepresentation_unitaryTorusDualInclusion
    (U : unitaryGroup ι ℂ) (s : ι → ℝ) :
    unitaryTorusRestriction ι (unitaryCoadjointRepresentation ι U (unitaryTorusDualInclusion ι s)) =
      fun k => ∑ i, ‖(U : Matrix ι ι ℂ) k i‖ ^ 2 * s i := by
  rw [unitaryTorusDualInclusion_apply, unitaryCoadjointRepresentation_unitaryTracePairing,
    unitaryTorusRestriction_unitaryTracePairing]
  ext k
  exact re_mul_diagonal_mul_star_apply_self (U : Matrix ι ι ℂ) s k

/-! ### Kostant's convexity theorem for `U(n)` -/

/-- **The torus moment image of a coadjoint orbit of `U(n)` is a permutohedron.** For a Hermitian
matrix `H`, the restrictions to the Lie algebra of the diagonal torus of the covectors in the
coadjoint orbit through `⟨H, ·⟩` form the convex hull of the rearrangements of the eigenvalues of
`H`. This is the Schur–Horn theorem, read through the trace pairing. -/
theorem range_unitaryTorusRestriction_unitaryCoadjointRepresentation {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) :
    Set.range (fun U : unitaryGroup ι ℂ => unitaryTorusRestriction ι
        (unitaryCoadjointRepresentation ι U (unitaryTracePairing ι ⟨H, hH.isSelfAdjoint⟩))) =
      convexHull ℝ (Set.range fun σ : Equiv.Perm ι => hH.eigenvalues ∘ σ) := by
  rw [← hH.range_re_diag_unitary_mul_mul_star (𝕜 := ℂ)]
  simp_rw [unitaryCoadjointRepresentation_unitaryTracePairing,
    unitaryTorusRestriction_unitaryTracePairing, RCLike.re_to_complex, Unitary.coe_star]

/-- **Kostant's convexity theorem for `U(n)`, permutohedron form.** For `ν = ⟨diag(s), ·⟩ ∈ 𝔱*`,
the torus moment image of the coadjoint orbit through `ν` is the convex hull of the rearrangements
of `s`. -/
theorem range_unitaryTorusRestriction_unitaryCoadjointRepresentation_unitaryTorusDualInclusion
    (s : ι → ℝ) :
    Set.range (fun U : unitaryGroup ι ℂ => unitaryTorusRestriction ι
        (unitaryCoadjointRepresentation ι U (unitaryTorusDualInclusion ι s))) =
      convexHull ℝ (Set.range fun σ : Equiv.Perm ι => s ∘ σ) := by
  rw [← range_re_diag_unitary_mul_diagonal_mul_star (𝕜 := ℂ)]
  simp_rw [unitaryTorusDualInclusion_apply, unitaryCoadjointRepresentation_unitaryTracePairing,
    unitaryTorusRestriction_unitaryTracePairing, RCLike.re_to_complex, Unitary.coe_star,
    RCLike.ofReal_eq_complex_ofReal]

section Weyl

variable {n : ℕ}

/-- **The Weyl group orbit of a covector in `𝔱*`.** For `ν = ⟨diag(s), ·⟩`, the torus restrictions
of the translates `Ad*_g ν` by the elements `g` of the normalizer of the diagonal torus are exactly
the rearrangements of `s`: the Weyl group `N(T) / T` acts on `𝔱*` by permuting coordinates. -/
theorem unitaryTorusRestriction_image_normalizer_unitaryTorus (s : Fin n → ℝ) :
    (fun g => unitaryTorusRestriction (Fin n)
        (unitaryCoadjointRepresentation (Fin n) g (unitaryTorusDualInclusion (Fin n) s))) ''
        (Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ))) =
      Set.range fun σ : Equiv.Perm (Fin n) => s ∘ σ := by
  -- The torus restriction of `Ad*_g ν` for `g = diag(z) P` with `P` the matrix of `σ⁻¹`.
  have key (z : Fin n → Circle) (σ : Equiv.Perm (Fin n)) :
      unitaryTorusRestriction (Fin n) (unitaryCoadjointRepresentation (Fin n)
        (unitaryTorusHom (Fin n) z * permutationUnitary σ) (unitaryTorusDualInclusion (Fin n) s)) =
        s ∘ ⇑σ⁻¹ := by
    rw [unitaryTorusRestriction_unitaryCoadjointRepresentation_unitaryTorusDualInclusion]
    ext k
    simp [coe_unitaryTorusHom_mul_permutationUnitary_apply, apply_ite]
  ext d
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨z, σ, rfl⟩ := mem_normalizer_unitaryTorus_iff.mp hg
    exact ⟨σ⁻¹, (key z σ).symm⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨permutationUnitary σ⁻¹, permutationUnitary_mem_normalizer σ⁻¹, ?_⟩
    have h := key 1 σ⁻¹
    rwa [map_one, one_mul, inv_inv] at h

/-- **Kostant's convexity theorem for `U(n)`.** For `ν = ⟨diag(s), ·⟩ ∈ 𝔱*`, the image of the
coadjoint orbit `K · ν` under the restriction to the Lie algebra of the diagonal torus is the convex
hull of the restrictions of the Weyl translates of `ν`, that is of its translates by the normalizer
of the torus: `pr_𝔱* (K · ν) = conv (pr_𝔱* (N(T) · ν))`. -/
theorem range_unitaryTorusRestriction_eq_convexHull_image_normalizer (s : Fin n → ℝ) :
    Set.range (fun U : unitaryGroup (Fin n) ℂ => unitaryTorusRestriction (Fin n)
        (unitaryCoadjointRepresentation (Fin n) U (unitaryTorusDualInclusion (Fin n) s))) =
      convexHull ℝ ((fun g => unitaryTorusRestriction (Fin n)
        (unitaryCoadjointRepresentation (Fin n) g (unitaryTorusDualInclusion (Fin n) s))) ''
          (Subgroup.normalizer (unitaryTorus (Fin n) : Set (unitaryGroup (Fin n) ℂ)))) := by
  rw [unitaryTorusRestriction_image_normalizer_unitaryTorus,
    range_unitaryTorusRestriction_unitaryCoadjointRepresentation_unitaryTorusDualInclusion]

end Weyl

end TauCeti
