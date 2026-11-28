/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Classification
import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# The Williamson type of a nondegenerate singular point

Let `F : E → G` be a `C²` map on a finite-dimensional symplectic vector space `(E, ω)`, the local
model of an integrable system near a point `x`, and write `U = ker dF_x`. The point `x` is
nondegenerate (`TauCeti.SymplecticForm.IsNondegeneratePoint`) when the Hessians at `x` of the
critical functions `ℓ ∘ F` descend to the transversal space `U ⧸ (U ∩ U^ω)` and form a
nondegenerate family there. By Williamson's classification, this family has a **Williamson type**
`(k_e, k_h, k_f)` (`TauCeti.SymplecticForm.HasWilliamsonType`): in suitable linear symplectic
coordinates on the transversal space its span is spanned by `k_e` elliptic blocks
`(xₖ² + yₖ²) / 2`, `k_h` hyperbolic blocks `xₖ yₖ` and `k_f` focus-focus pairs. This file defines
the type of the point as the type of this family
(`TauCeti.SymplecticForm.HasWilliamsonTypeAt ω F x k_e k_h k_f`), and proves:

* every nondegenerate point has a Williamson type
  (`TauCeti.SymplecticForm.IsNondegeneratePoint.exists_hasWilliamsonTypeAt`), and a point with a
  type is nondegenerate (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.isNondegeneratePoint`);
* the type is unique (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.unique`);
* if the functions `ℓ ∘ F` Poisson-commute at `x`, `dim E = 2 n` and `dF_x` has rank `r`, then
  `k_e + k_h + 2 k_f = n - r`
  (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.two_mul_add_add_add_finrank_range_eq_finrank`);
* the type does not depend on the choice of coordinates on the target: it is unchanged when `F`
  is composed with a `C²` map `g` whose differential at `F x` has a continuous linear left inverse
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_comp_iff`), and in particular with a continuous
  linear equivalence `A`
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_continuousLinearEquiv_comp_iff`), for instance the
  matrix `A ∈ GL(n, ℝ)` that makes the first `r` components of `A ∘ F` independent at `x` and the
  others critical;
* at a critical point the transversal space is `E` itself, and the type of the point is the type
  of the family of Hessians of the functions `ℓ ∘ F` on `E`
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_iff_of_fderiv_eq_zero`), with
  `k_e + k_h + 2 k_f = n`
  (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.two_mul_add_add_eq_finrank_of_fderiv_eq_zero`);
* the type does not depend on the choice of symplectic coordinates on the source either: if
  `φ : E' → E` is `C²` at `y` and its differential there is a linear symplectomorphism, for
  instance a canonical transformation, then `y` has type `(k_e, k_h, k_f)` for `F ∘ φ` exactly when
  `φ y` has this type for `F`
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_comp_right_iff_of_isSymplectomorphism`).

The type is a property of the differential `dF_x` and of the Hessians of the functions `ℓ ∘ F`
alone. This unbundled content
(`TauCeti.SymplecticForm.HasTransversalWilliamsonType ω T Q k_e k_h k_f`, for a linear map `T` and
a family `Q` of quadratic forms) is shared with the Williamson type of a point of a map on a
symplectic manifold (`TauCeti.SmoothTwoForm.IsNondegenerate.HasWilliamsonTypeAt`), and it is
transported along linear symplectomorphisms
(`TauCeti.SymplecticForm.hasTransversalWilliamsonType_comp_iff`): a linear symplectomorphism
`e` carries `ker (T ∘ e)` onto `ker T` and induces a symplectomorphism of the reduced spaces through
which the reduced forms correspond, and the Williamson type of a family is invariant under
symplectomorphisms (`TauCeti.SymplecticForm.hasWilliamsonType_comp_iff`).

## Main definitions

* `TauCeti.SymplecticForm.HasTransversalWilliamsonType ω T Q k_e k_h k_f`: the forms `Q ℓ` with
  `ℓ ∘ T = 0` descend to the reduced space of `ker T` and have Williamson type `(k_e, k_h, k_f)`
  there.
* `TauCeti.SymplecticForm.HasWilliamsonTypeAt ω F x k_e k_h k_f`: `x` is a nondegenerate point of
  `F` with `k_e` elliptic, `k_h` hyperbolic and `k_f` focus-focus components.

## References

* E. Miranda and N. T. Zung, *Equivariant normal form for nondegenerate singular orbits of
  integrable Hamiltonian systems*, Annales scientifiques de l'École Normale Supérieure 37 (2004),
  819–839, Sections 2.1–2.3.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
-/

public section

noncomputable section

open Module

namespace TauCeti.SymplecticForm

/-! ### The Williamson type of transversal data -/

section Transversal

variable {V V' G : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [FiniteDimensional ℝ V] [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V']
  [FiniteDimensional ℝ V'] [NormedAddCommGroup G] [NormedSpace ℝ G] {kₑ kₕ k_f : ℕ}

/-- The common content of the linear and the manifold notion of the Williamson type of a point,
for the differential `T` of the map and the Hessians `Q ℓ` of the functions `ℓ ∘ F`: `(T, Q)` is
transversally nondegenerate, and the forms `Q ℓ` with `ℓ ∘ T = 0`, descended to the reduced space
of `ker T`, have Williamson type `(kₑ, kₕ, k_f)`. -/
def HasTransversalWilliamsonType (ω₁ : SymplecticForm V) (T : V →L[ℝ] G)
    (Q : (G →L[ℝ] ℝ) → QuadraticForm ℝ V) (kₑ kₕ k_f : ℕ) : Prop :=
  ∃ h : IsTransversallyNondegenerate ω₁ T Q,
    (ω₁.reduction T.ker).HasWilliamsonType
      (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦
        ω₁.reducedQuadraticForm _ (Q ℓ.val) (h.polar_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f

/-- Unfolding `HasTransversalWilliamsonType`. -/
theorem hasTransversalWilliamsonType_iff {ω₁ : SymplecticForm V} {T : V →L[ℝ] G}
    {Q : (G →L[ℝ] ℝ) → QuadraticForm ℝ V} :
    HasTransversalWilliamsonType ω₁ T Q kₑ kₕ k_f ↔ ∃ h : IsTransversallyNondegenerate ω₁ T Q,
      (ω₁.reduction T.ker).HasWilliamsonType
        (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦
          ω₁.reducedQuadraticForm _ (Q ℓ.val) (h.polar_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f :=
  Iff.rfl

/-- Transversal data with a Williamson type are transversally nondegenerate. -/
theorem HasTransversalWilliamsonType.isTransversallyNondegenerate {ω₁ : SymplecticForm V}
    {T : V →L[ℝ] G} {Q : (G →L[ℝ] ℝ) → QuadraticForm ℝ V}
    (h : HasTransversalWilliamsonType ω₁ T Q kₑ kₕ k_f) : IsTransversallyNondegenerate ω₁ T Q :=
  h.1

/-- **Transport of the transversal Williamson type along a linear symplectomorphism.** Let
`e : V ≃ V'` carry `ω₁` to `ω₂` and let `T : V' → G` be linear. If the forms `Q' ℓ` on `V` are the
pullbacks along `e` of the forms `Q ℓ` on `V'` whenever `ℓ ∘ T = 0`, then `(T ∘ e, Q')` has
Williamson type `(kₑ, kₕ, k_f)` for `ω₁` exactly when `(T, Q)` has this type for `ω₂`: `e`
induces a symplectomorphism of the reduced spaces of `ker (T ∘ e)` and `ker T` through which the
reduced forms correspond. -/
theorem hasTransversalWilliamsonType_comp_iff {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm V'}
    (e : V ≃L[ℝ] V') (he : IsSymplectomorphism ω₁ ω₂ e.toLinearEquiv) (T : V' →L[ℝ] G)
    {Q : (G →L[ℝ] ℝ) → QuadraticForm ℝ V'} {Q' : (G →L[ℝ] ℝ) → QuadraticForm ℝ V}
    (hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → Q' ℓ = (Q ℓ).comp (e.toLinearEquiv : V →ₗ[ℝ] V')) :
    HasTransversalWilliamsonType ω₁ (T.comp (e : V →L[ℝ] V')) Q' kₑ kₕ k_f ↔
      HasTransversalWilliamsonType ω₂ T Q kₑ kₕ k_f := by
  have hnd := isTransversallyNondegenerate_comp_iff e he T hQ
  -- Once both families descend, they agree up to a symplectomorphism of the reduced spaces.
  have key (h' : IsTransversallyNondegenerate ω₁ (T.comp (e : V →L[ℝ] V')) Q')
      (h : IsTransversallyNondegenerate ω₂ T Q) :
      (ω₁.reduction (T.comp (e : V →L[ℝ] V')).ker).HasWilliamsonType
          (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (T.comp (e : V →L[ℝ] V')) = 0} ↦
            ω₁.reducedQuadraticForm _ (Q' ℓ.val) (h'.polar_eq_zero ℓ.val ℓ.property))
          kₑ kₕ k_f ↔
        (ω₂.reduction T.ker).HasWilliamsonType
          (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦
            ω₂.reducedQuadraticForm _ (Q ℓ.val) (h.polar_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f := by
    obtain ⟨c, hc, hr⟩ := exists_isSymplectomorphism_range_reducedQuadraticForm_eq e he T hQ
      h.polar_eq_zero h'.polar_eq_zero
    rw [← hasWilliamsonType_comp_iff hc]
    exact hasWilliamsonType_iff_of_span_eq (congrArg _ hr)
  exact ⟨fun ⟨h', ht⟩ ↦ ⟨hnd.1 h', (key h' (hnd.1 h')).1 ht⟩,
    fun ⟨h, ht⟩ ↦ ⟨hnd.2 h, (key (hnd.2 h) h).2 ht⟩⟩

end Transversal

/-! ### The Williamson type of a point -/

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {ι : Type*} {kₑ kₕ k_f : ℕ}

variable (ω : SymplecticForm E) in
/-- A point `x` has **Williamson type** `(kₑ, kₕ, k_f)` for a `C²` map `F : E → G` on a symplectic
vector space `(E, ω)` when it is a nondegenerate point of `F` and the family of transversal
Hessians, the Hessians at `x` of the critical functions `ℓ ∘ F` descended to the transversal space
`U ⧸ (U ∩ U^ω)`, `U = ker dF_x`, has Williamson type `(kₑ, kₕ, k_f)`: in suitable Darboux
coordinates of the transversal space it spans the same space as `kₑ` elliptic blocks, `kₕ`
hyperbolic blocks and `k_f` focus-focus pairs. -/
def HasWilliamsonTypeAt (F : E → G) (x : E) (kₑ kₕ k_f : ℕ) : Prop :=
  ∃ h : ω.IsNondegeneratePoint F x,
    (ω.reduction (fderiv ℝ F x).ker).HasWilliamsonType
      (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
        ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.val ∘ F) x)
          (h.polar_hessianQuadraticForm_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f

variable {ω : SymplecticForm E} {F : E → G} {x : E}

/-- Unfolding `HasWilliamsonTypeAt`. -/
theorem hasWilliamsonTypeAt_iff :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ∃ h : ω.IsNondegeneratePoint F x,
      (ω.reduction (fderiv ℝ F x).ker).HasWilliamsonType
        (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
          ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.val ∘ F) x)
            (h.polar_hessianQuadraticForm_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f :=
  Iff.rfl

/-- A point with a Williamson type is a nondegenerate point. -/
theorem HasWilliamsonTypeAt.isNondegeneratePoint (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f) :
    ω.IsNondegeneratePoint F x :=
  h.1

/-- **Existence of the Williamson type of a nondegenerate point.** Every nondegenerate point of `F`
has a Williamson type: by Williamson's classification on the transversal space, its transversal
Hessians span the same space as elliptic, hyperbolic and focus-focus blocks. -/
theorem IsNondegeneratePoint.exists_hasWilliamsonTypeAt (h : ω.IsNondegeneratePoint F x) :
    ∃ kₑ kₕ k_f, ω.HasWilliamsonTypeAt F x kₑ kₕ k_f :=
  let ⟨kₑ, kₕ, k_f, ht⟩ := h.isNondegenerateQuadraticFamily.exists_hasWilliamsonType
  ⟨kₑ, kₕ, k_f, h, ht⟩

/-- A point is nondegenerate exactly when it has a Williamson type. -/
theorem isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt :
    ω.IsNondegeneratePoint F x ↔ ∃ kₑ kₕ k_f, ω.HasWilliamsonTypeAt F x kₑ kₕ k_f :=
  ⟨IsNondegeneratePoint.exists_hasWilliamsonTypeAt,
    fun ⟨_, _, _, h⟩ ↦ h.isNondegeneratePoint⟩

/-- **Uniqueness of the Williamson type of a point.** The numbers of elliptic, hyperbolic and
focus-focus components of a nondegenerate point are well defined. -/
theorem HasWilliamsonTypeAt.unique {kₑ' kₕ' k_f' : ℕ} (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f)
    (h' : ω.HasWilliamsonTypeAt F x kₑ' kₕ' k_f') : kₑ = kₑ' ∧ kₕ = kₕ' ∧ k_f = k_f' :=
  h.2.unique h'.2

/-- **The Williamson type and the rank.** If the functions `ℓ ∘ F` Poisson-commute at `x`, a
point of Williamson type `(kₑ, kₕ, k_f)` at which `dF_x` has rank `r` on a space of dimension
`2 n` satisfies `kₑ + kₕ + 2 k_f = n - r`: the transversal space has dimension `2 (n - r)`. -/
theorem HasWilliamsonTypeAt.two_mul_add_add_add_finrank_range_eq_finrank
    (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f)
    (hcomm : ∀ ℓ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ ∘ F) (ℓ' ∘ F) x = 0) :
    2 * (kₑ + kₕ + 2 * k_f + finrank ℝ (fderiv ℝ F x).range) = finrank ℝ E := by
  have hd := ω.finrank_reducedSpace_ker_fderiv
    (h.isNondegeneratePoint.contDiffAt.differentiableAt two_ne_zero) hcomm
  have ht := h.2.two_mul_add_add_eq_finrank
  omega

/-- **Williamson types of critical points.** At a critical point of `F`, `x` has Williamson type
`(kₑ, kₕ, k_f)` exactly when it is a nondegenerate rank-zero point and the Hessians of the
functions `ℓ ∘ F`, on the whole space `E`, form a family of Williamson type `(kₑ, kₕ, k_f)`. -/
theorem hasWilliamsonTypeAt_iff_of_fderiv_eq_zero (h0 : fderiv ℝ F x = 0) :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ω.IsNondegenerateRankZeroPoint F x ∧
      ω.HasWilliamsonType (fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x) kₑ kₕ k_f := by
  have hker : (fderiv ℝ F x).ker = ⊤ := by
    rw [h0]
    exact LinearMap.ker_zero
  have key (hx : ω.IsNondegeneratePoint F x) :=
    (hasWilliamsonType_reduction_iff_of_eq_top (kₑ := kₑ) (kₕ := kₕ) (k_f := k_f) hker _
      fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
        hx.polar_hessianQuadraticForm_eq_zero ℓ.val ℓ.property).trans
      (hasWilliamsonType_iff_of_span_eq (span_range_hessianQuadraticForm_of_fderiv_eq_zero h0))
  have hnd := isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (ω := ω) h0
  exact ⟨fun ⟨hx, ht⟩ ↦ ⟨hnd.1 hx, (key hx).1 ht⟩,
    fun ⟨hx, ht⟩ ↦ ⟨hnd.2 hx, (key (hnd.2 hx)).2 ht⟩⟩

/-- **The Williamson type of a critical point fills the dimension.** At a critical point of
Williamson type `(kₑ, kₕ, k_f)` on a space of dimension `2 n`, `kₑ + kₕ + 2 k_f = n`. -/
theorem HasWilliamsonTypeAt.two_mul_add_add_eq_finrank_of_fderiv_eq_zero
    (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f) (h0 : fderiv ℝ F x = 0) :
    2 * (kₑ + kₕ + 2 * k_f) = finrank ℝ E :=
  ((hasWilliamsonTypeAt_iff_of_fderiv_eq_zero h0).1 h).2.two_mul_add_add_eq_finrank

/-- Unbundled form of `HasWilliamsonTypeAt`, with the kernel of `dF_x` replaced by any `U` equal
to it. -/
private theorem hasWilliamsonTypeAt_iff_of_ker_eq {U : Submodule ℝ E}
    (hU : (fderiv ℝ F x).ker = U) :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ω.IsNondegeneratePoint F x ∧
      ∃ hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (fderiv ℝ F x) = 0 → ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0,
        (ω.reduction U).HasWilliamsonType
          (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
            ω.reducedQuadraticForm U _ (hQ ℓ.val ℓ.property)) kₑ kₕ k_f := by
  subst hU
  exact ⟨fun ⟨h, ht⟩ ↦ ⟨h, h.polar_hessianQuadraticForm_eq_zero, ht⟩, fun ⟨h, _, ht⟩ ↦ ⟨h, ht⟩⟩

/-- Unbundled form of `HasWilliamsonTypeAt`, with the derivative `dF_x` replaced by any `T` equal
to it: `F` is `C²` at `x` and `(T, Q)` has Williamson type `(kₑ, kₕ, k_f)` for the Hessians `Q ℓ`
of the functions `ℓ ∘ F`. -/
theorem hasWilliamsonTypeAt_iff_of_fderiv_eq {T : E →L[ℝ] G} (hT : fderiv ℝ F x = T) :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ContDiffAt ℝ 2 F x ∧
      HasTransversalWilliamsonType ω T (fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x)
        kₑ kₕ k_f := by
  subst hT
  exact ⟨fun ⟨h, ht⟩ ↦ ⟨h.contDiffAt,
      ⟨h.polar_hessianQuadraticForm_eq_zero, h.isNondegenerateQuadraticFamily⟩, ht⟩,
    fun ⟨h₁, ⟨h₂, h₃⟩, ht⟩ ↦ ⟨⟨h₁, h₂, h₃⟩, ht⟩⟩

/-- **Invariance of the Williamson type under reparametrization of the values.** Composing `F` with
a `C²` map `g` whose differential `Dg` at `F x` has a continuous linear left inverse does not change
the Williamson type of a point: the kernel of the differential, and hence the transversal space, is
the same, and the transversal Hessians of `g ∘ F` span the same space as those of `F`
(`TauCeti.SymplecticForm.span_range_reducedQuadraticForm_hessianQuadraticForm_comp_eq`). -/
theorem hasWilliamsonTypeAt_comp_iff {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {g : G → G'} (hg : ContDiffAt ℝ 2 g (F x)) (hD : (fderiv ℝ g (F x)).HasLeftInverse)
    (hF : ContDiffAt ℝ 2 F x) :
    ω.HasWilliamsonTypeAt (g ∘ F) x kₑ kₕ k_f ↔ ω.HasWilliamsonTypeAt F x kₑ kₕ k_f := by
  rw [hasWilliamsonTypeAt_iff_of_ker_eq (ker_fderiv_comp_of_injective
      (hg.differentiableAt two_ne_zero) hD.injective (hF.differentiableAt two_ne_zero)),
    hasWilliamsonTypeAt_iff_of_ker_eq rfl]
  exact and_congr (isNondegeneratePoint_comp_iff hg hD hF)
    ((Equiv.ofIff (forall_polar_hessianQuadraticForm_comp_eq_zero_iff hg hD hF)).exists_congr
      fun hQ' ↦ hasWilliamsonType_iff_of_span_eq
        (span_range_reducedQuadraticForm_hessianQuadraticForm_comp_eq hg hD hF hQ' _))

/-- **Invariance of the Williamson type under linear changes of the values.** Composing `F` with a
continuous linear equivalence `A : G ≃ G'` does not change the Williamson type of a point. Unlike
`hasWilliamsonTypeAt_comp_iff`, no regularity of `F` is assumed: `F` is `C²` at `x` exactly when
`A ∘ F` is. -/
@[simp]
theorem hasWilliamsonTypeAt_continuousLinearEquiv_comp_iff {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G'] (A : G ≃L[ℝ] G') :
    ω.HasWilliamsonTypeAt (A ∘ F) x kₑ kₕ k_f ↔ ω.HasWilliamsonTypeAt F x kₑ kₕ k_f := by
  by_cases hF : ContDiffAt ℝ 2 F x
  · exact hasWilliamsonTypeAt_comp_iff (A : G →L[ℝ] G').contDiff.contDiffAt
      (A.hasLeftInverse.congr A.fderiv) hF
  exact iff_of_false (fun h ↦ hF (A.comp_contDiffAt_iff.1 h.isNondegeneratePoint.contDiffAt))
    fun h ↦ hF h.isNondegeneratePoint.contDiffAt

/-- **Invariance of the Williamson type under canonical transformations.** Let `φ : E' → E` be
`C²` at `y`, with differential at `y` a linear symplectomorphism `e` from `(E', ω')` to `(E, ω)`.
Then `y` has Williamson type `(kₑ, kₕ, k_f)` for `F ∘ φ` and `ω'` exactly when `φ y` has this type
for `F` and `ω`: `e` carries the kernel of the differential of `F ∘ φ` onto that of `F`, and the
induced symplectomorphism of transversal spaces carries the transversal Hessians of `F` to those
of `F ∘ φ`. Only the differential of `φ` at `y` enters, so this applies in particular to a `C²`
canonical transformation `φ`, and to a linear change of symplectic coordinates. -/
theorem hasWilliamsonTypeAt_comp_right_iff_of_isSymplectomorphism {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {ω' : SymplecticForm E'}
    {φ : E' → E} {y : E'} {e : E' ≃ₗ[ℝ] E} (he : IsSymplectomorphism ω' ω e)
    (hφ : ContDiffAt ℝ 2 φ y) (hφe : ∀ v, fderiv ℝ φ y v = e v) :
    ω'.HasWilliamsonTypeAt (F ∘ φ) y kₑ kₕ k_f ↔ ω.HasWilliamsonTypeAt F (φ y) kₑ kₕ k_f := by
  by_cases hF : ContDiffAt ℝ 2 F (φ y)
  swap
  · exact iff_of_false (fun h ↦ hF ((isNondegeneratePoint_comp_right_iff_of_isSymplectomorphism
      he hφ hφe).1 h.isNondegeneratePoint).contDiffAt) fun h ↦ hF h.isNondegeneratePoint.contDiffAt
  obtain ⟨e', he', hT, hQ⟩ := exists_isSymplectomorphism_of_comp_right he hφ hφe hF
  rw [hasWilliamsonTypeAt_iff_of_fderiv_eq hT, hasWilliamsonTypeAt_iff_of_fderiv_eq rfl,
    hasTransversalWilliamsonType_comp_iff e' he' _ hQ]
  exact and_congr_left' (iff_of_true (hF.comp y hφ) hF)

end TauCeti.SymplecticForm
