/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Topology.Grassmannian.Orthonormal
public import TauCeti.Topology.VectorBundle.IdempotentRange

/-!
# The tautological bundle of a finite Grassmannian and its orthogonal complement

Let `𝕜` be `ℝ` or `ℂ` (more generally `RCLike 𝕜`). A point `V` of the finite Grassmannian
`TauCeti.finiteGrassmannian 𝕜 r N` is an `r`-dimensional subspace of `Fin N → 𝕜`; transported
along the native coordinate identification `WithLp.toLp 2`, it is the subspace
`V.toEuclidean` of `EuclideanSpace 𝕜 (Fin N)`. The orthogonal projections
`V.toEuclidean.starProjection` form a continuous family of idempotent operators on
`EuclideanSpace 𝕜 (Fin N)` (`TauCeti.finiteGrassmannian.continuous_starProjection_toEuclidean`).
Continuity is checked on orthonormal frames: the finite Grassmannian carries the quotient
topology of the span map on orthonormal frames, and for an orthonormal frame `f` the projection
onto its span is `x ↦ ∑ i, ⟪f i, x⟫ • f i` (`Orthonormal.starProjection_apply_eq_sum`).

The image bundle of this family of projections is the tautological bundle
`TauCeti.finiteGrassmannian.Tautological 𝕜 r N`: its fibre over `V` is the range of the
orthogonal projection onto `V`, which is `V.toEuclidean` itself (Mathlib's
`Submodule.range_starProjection`). The complementary projections `1 - p` give the orthogonal
complement bundle `TauCeti.finiteGrassmannian.TautologicalOrthogonal 𝕜 r N`, whose fibre over `V`
is `V.toEuclideanᗮ` (`TauCeti.finiteGrassmannian.range_one_sub_starProjection_toEuclidean`).
They are topological vector bundles of ranks `r` and `N - r`, with model fibres `Fin r → 𝕜` and
`Fin (N - r) → 𝕜` and with the topology of subspaces of the trivial bundle
`finiteGrassmannian 𝕜 r N × EuclideanSpace 𝕜 (Fin N)`. Adding the two components identifies their
direct sum with that trivial bundle
(`TauCeti.finiteGrassmannian.tautologicalProdOrthogonalHomeomorph`): `γ ⊕ γ⊥ ≅ 𝕜ᴺ`.
These are the bundles whose pullbacks along maps into finite Grassmannians represent vector
bundles in the classification of bundles over compact bases; that classification is not proved
here.

The bundle structures are those of `TauCeti.rangeFiberBundle` and `TauCeti.rangeVectorBundle`,
and the direct-sum comparison is `TauCeti.rangeProdRangeOneSubHomeomorph`, applied to this
continuous family of projections.

## Main definitions

* `TauCeti.finiteGrassmannian.toEuclidean`: a point of the Grassmannian as a subspace of
  `EuclideanSpace 𝕜 (Fin N)`.
* `TauCeti.finiteGrassmannian.Tautological`: the tautological bundle `γ`.
* `TauCeti.finiteGrassmannian.TautologicalOrthogonal`: its orthogonal complement `γ⊥`.
* `TauCeti.finiteGrassmannian.tautologicalProdOrthogonalHomeomorph`: `γ ⊕ γ⊥` is homeomorphic to
  the trivial bundle with fibre `EuclideanSpace 𝕜 (Fin N)`, linearly on each fibre.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, for the tautological bundle
  `γ^r(ℝ^N)` over the Grassmannian and its orthogonal complement.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, where local triviality of the tautological
  bundle is likewise proved with orthogonal projections.
-/

public section

open Bundle Module Set

namespace TauCeti

namespace finiteGrassmannian

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-- A point `V` of the finite Grassmannian, an `r`-dimensional subspace of `Fin N → 𝕜`,
transported to a subspace of `EuclideanSpace 𝕜 (Fin N)` by the coordinate identification. -/
def toEuclidean (V : finiteGrassmannian 𝕜 r N) : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)) :=
  V.1.comap (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).toLinearMap

@[simp] theorem mem_toEuclidean {V : finiteGrassmannian 𝕜 r N} {x : EuclideanSpace 𝕜 (Fin N)} :
    x ∈ V.toEuclidean ↔ WithLp.ofLp x ∈ V.1 := Iff.rfl

/-- Distinct points of the Grassmannian give distinct Euclidean subspaces. -/
theorem toEuclidean_injective :
    Function.Injective (toEuclidean : finiteGrassmannian 𝕜 r N → _) := fun V W h ↦ by
  refine Subtype.ext <| Submodule.ext fun x ↦ ?_
  simpa using SetLike.ext_iff.1 h (WithLp.toLp 2 x)

/-- The transported subspace still has dimension `r`. -/
@[simp] theorem finrank_toEuclidean (V : finiteGrassmannian 𝕜 r N) :
    finrank 𝕜 V.toEuclidean = r := by
  rw [toEuclidean, Submodule.comap_equiv_eq_map_symm]
  exact ((WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.finrank_map_eq V.1).trans V.2

/-- The orthogonal complement of `V` in `EuclideanSpace 𝕜 (Fin N)` has dimension `N - r`. -/
@[simp] theorem finrank_orthogonal_toEuclidean (V : finiteGrassmannian 𝕜 r N) :
    finrank 𝕜 V.toEuclideanᗮ = N - r := by
  have h := V.toEuclidean.finrank_add_finrank_orthogonal
  rw [finrank_toEuclidean, finrank_euclideanSpace_fin] at h
  omega

/-- The span of a frame, transported to `EuclideanSpace 𝕜 (Fin N)`, is the span of the transported
vectors. -/
theorem toEuclidean_frameSpan (f : finiteFullRankFrame 𝕜 r N) :
    (frameSpan f).toEuclidean =
      Submodule.span 𝕜 (range fun i ↦ (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N))) := by
  rw [toEuclidean, coe_frameSpan, Submodule.comap_equiv_eq_map_symm, Submodule.map_span,
    ← range_comp]
  simp [Function.comp_def]

/-- The orthogonal projection onto a point of the finite Grassmannian depends continuously on
the point. -/
@[fun_prop]
theorem continuous_starProjection_toEuclidean :
    Continuous fun V : finiteGrassmannian 𝕜 r N ↦ V.toEuclidean.starProjection := by
  -- Test continuity on orthonormal frames `f`, where the projection onto the span is
  -- `x ↦ ∑ i, ⟪f i, x⟫ • f i`; the Grassmannian is a quotient of the orthonormal frames.
  refine isQuotientMap_frameSpan_toFullRankFrame.continuous_iff.2 <|
    continuous_clm_apply.2 fun x ↦ ?_
  have he (i : Fin r) : Continuous fun f : finiteOrthonormalFrame 𝕜 r N ↦
      (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N)) :=
    (PiLp.continuous_toLp 2 _).comp ((continuous_apply i).comp continuous_subtype_val)
  have hsum (f : finiteOrthonormalFrame 𝕜 r N) :
      (frameSpan f.toFullRankFrame).toEuclidean.starProjection x =
        ∑ i, inner 𝕜 (WithLp.toLp 2 (f.1 i) : EuclideanSpace 𝕜 (Fin N)) x •
          WithLp.toLp 2 (f.1 i) :=
    f.2.starProjection_apply_eq_sum (by
      rw [toEuclidean_frameSpan, finiteOrthonormalFrame.coe_toFullRankFrame]) x
  simp only [Function.comp_def, hsum]
  exact continuous_finsetSum _ fun i _ ↦ by have := he i; fun_prop

/-- The range of the complementary projection is the orthogonal complement. -/
theorem range_one_sub_starProjection_toEuclidean (V : finiteGrassmannian 𝕜 r N) :
    (1 - V.toEuclidean.starProjection).range = V.toEuclideanᗮ := by
  rw [← Submodule.starProjection_orthogonal', Submodule.range_starProjection]

/-- The complementary projections `1 - p` depend continuously on the point of the Grassmannian. -/
theorem continuous_one_sub_starProjection_toEuclidean :
    Continuous fun V : finiteGrassmannian 𝕜 r N ↦ 1 - V.toEuclidean.starProjection :=
  continuous_const.sub continuous_starProjection_toEuclidean

variable (𝕜 r N)

/-- The **tautological bundle** `γ` over the finite Grassmannian: its fibre over `V` is the range
of the orthogonal projection onto `V`, that is, `V` itself as a subspace of
`EuclideanSpace 𝕜 (Fin N)` (`Submodule.range_starProjection`). -/
abbrev Tautological : finiteGrassmannian 𝕜 r N → Type _ :=
  fun V ↦ V.toEuclidean.starProjection.range

/-- The orthogonal complement `γ⊥` of the tautological bundle over the finite Grassmannian: its
fibre over `V` is the range of `1 - p`, for `p` the orthogonal projection onto `V`, that is, the
orthogonal complement of `V` in `EuclideanSpace 𝕜 (Fin N)`
(`TauCeti.finiteGrassmannian.range_one_sub_starProjection_toEuclidean`). -/
abbrev TautologicalOrthogonal : finiteGrassmannian 𝕜 r N → Type _ :=
  fun V ↦ (1 - V.toEuclidean.starProjection).range

/- The fibre dimensions are computed through `LinearEquiv.ofEq`: neither `simp` nor `rw` can
rewrite the submodule inside the dependent type `↥(p V).range`. -/
/-- Every fibre of the tautological bundle is isomorphic to the model fibre `Fin r → 𝕜`. -/
theorem nonempty_continuousLinearEquiv_tautological (V : finiteGrassmannian 𝕜 r N) :
    Nonempty ((Fin r → 𝕜) ≃L[𝕜] Tautological 𝕜 r N V) :=
  FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq <| (finrank_fin_fun 𝕜).trans <|
    (finrank_toEuclidean V).symm.trans
      (LinearEquiv.ofEq _ _ (Submodule.range_starProjection _)).finrank_eq.symm

/-- Every fibre of the orthogonal complement of the tautological bundle is isomorphic to the model
fibre `Fin (N - r) → 𝕜`. -/
theorem nonempty_continuousLinearEquiv_tautologicalOrthogonal (V : finiteGrassmannian 𝕜 r N) :
    Nonempty ((Fin (N - r) → 𝕜) ≃L[𝕜] TautologicalOrthogonal 𝕜 r N V) :=
  FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq <| (finrank_fin_fun 𝕜).trans <|
    (finrank_orthogonal_toEuclidean V).symm.trans
      (LinearEquiv.ofEq _ _ (range_one_sub_starProjection_toEuclidean V)).finrank_eq.symm

/-- The tautological bundle is a fibre bundle with model fibre `Fin r → 𝕜`, its total space
carrying the topology of a subspace of `finiteGrassmannian 𝕜 r N × EuclideanSpace 𝕜 (Fin N)`. -/
noncomputable instance : FiberBundle (Fin r → 𝕜) (Tautological 𝕜 r N) :=
  rangeFiberBundle continuous_starProjection_toEuclidean
    (fun V ↦ V.toEuclidean.isIdempotentElem_starProjection)
    (nonempty_continuousLinearEquiv_tautological 𝕜 r N)

/-- The tautological bundle is a topological vector bundle of rank `r`. -/
instance : VectorBundle 𝕜 (Fin r → 𝕜) (Tautological 𝕜 r N) :=
  rangeVectorBundle continuous_starProjection_toEuclidean
    (fun V ↦ V.toEuclidean.isIdempotentElem_starProjection)
    (nonempty_continuousLinearEquiv_tautological 𝕜 r N)

/-- The orthogonal complement of the tautological bundle is a fibre bundle with model fibre
`Fin (N - r) → 𝕜`, its total space carrying the topology of a subspace of
`finiteGrassmannian 𝕜 r N × EuclideanSpace 𝕜 (Fin N)`. -/
noncomputable instance : FiberBundle (Fin (N - r) → 𝕜) (TautologicalOrthogonal 𝕜 r N) :=
  rangeFiberBundle continuous_one_sub_starProjection_toEuclidean
    (fun V ↦ V.toEuclidean.isIdempotentElem_starProjection.one_sub)
    (nonempty_continuousLinearEquiv_tautologicalOrthogonal 𝕜 r N)

/-- The orthogonal complement of the tautological bundle is a topological vector bundle of rank
`N - r`. -/
instance : VectorBundle 𝕜 (Fin (N - r) → 𝕜) (TautologicalOrthogonal 𝕜 r N) :=
  rangeVectorBundle continuous_one_sub_starProjection_toEuclidean
    (fun V ↦ V.toEuclidean.isIdempotentElem_starProjection.one_sub)
    (nonempty_continuousLinearEquiv_tautologicalOrthogonal 𝕜 r N)

/-- **The tautological bundle and its orthogonal complement sum to a trivial bundle**:
`γ ⊕ γ⊥ ≅ 𝕜ᴺ`. Adding the two components is a homeomorphism from the total space of the direct
sum onto `finiteGrassmannian 𝕜 r N × EuclideanSpace 𝕜 (Fin N)`, over the identity of the
Grassmannian and linear on each fibre. -/
noncomputable def tautologicalProdOrthogonalHomeomorph :
    TotalSpace ((Fin r → 𝕜) × (Fin (N - r) → 𝕜))
        (Tautological 𝕜 r N ×ᵇ TautologicalOrthogonal 𝕜 r N) ≃ₜ
      finiteGrassmannian 𝕜 r N × EuclideanSpace 𝕜 (Fin N) :=
  rangeProdRangeOneSubHomeomorph _ _ continuous_starProjection_toEuclidean
    fun V ↦ V.toEuclidean.isIdempotentElem_starProjection

variable {𝕜 r N}

/- The two evaluation lemmas are not `simp` lemmas, for the reason given at
`TauCeti.rangeProdRangeOneSubHomeomorph_apply`: `simp` would rewrite inside the fibre types. -/

/-- The comparison `γ ⊕ γ⊥ ≅ 𝕜ᴺ` adds the two components of a vector of the direct sum. -/
theorem tautologicalProdOrthogonalHomeomorph_apply
    (v : TotalSpace ((Fin r → 𝕜) × (Fin (N - r) → 𝕜))
      (Tautological 𝕜 r N ×ᵇ TautologicalOrthogonal 𝕜 r N)) :
    tautologicalProdOrthogonalHomeomorph 𝕜 r N v =
      (v.proj, (v.2.1 : EuclideanSpace 𝕜 (Fin N)) + v.2.2) :=
  rangeProdRangeOneSubHomeomorph_apply _ _ _ _ v

/-- The inverse of `γ ⊕ γ⊥ ≅ 𝕜ᴺ` splits a vector by the orthogonal projections onto `V` and onto
its orthogonal complement. -/
theorem tautologicalProdOrthogonalHomeomorph_symm_apply
    (q : finiteGrassmannian 𝕜 r N × EuclideanSpace 𝕜 (Fin N)) :
    (tautologicalProdOrthogonalHomeomorph 𝕜 r N).symm q =
      ⟨q.1, (q.1.toEuclidean.starProjection.rangeRestrict q.2,
        (1 - q.1.toEuclidean.starProjection).rangeRestrict q.2)⟩ :=
  rangeProdRangeOneSubHomeomorph_symm_apply _ _ _ _ q

end finiteGrassmannian

end TauCeti
