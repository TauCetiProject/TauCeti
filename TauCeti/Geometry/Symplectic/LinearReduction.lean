/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions

/-!
# Linear symplectic reduction

Let `ω` be a linear symplectic form on a real vector space `V` and `U` a subspace. The restriction
of `ω` to `U` is in general degenerate: its kernel is `U ∩ U^ω`. Dividing it out gives the
**reduced space** `U ⧸ (U ∩ U^ω)` (`TauCeti.SymplecticForm.ReducedSpace ω U`), on which `ω`
descends to a symplectic form (`TauCeti.SymplecticForm.reduction ω U`),
`ω_red([u], [v]) = ω(u, v)`. This is the pointwise linear algebra underlying symplectic reduction:

* for a coisotropic `U` (a regular level of a moment map at a fixed value, say) the reduced space is
  `U ⧸ U^ω`, of dimension `2 dim U - dim V`;
* for an arbitrary `W`, the reduction of `U = W^ω` is the symplectic normal space
  `W^ω ⧸ (W ∩ W^ω)` of the local normal form of Hamiltonian actions, where `W` is the tangent space
  of an orbit; it has dimension `dim V - dim W - dim (W ∩ W^ω)`.

The construction is functorial: a linear symplectomorphism carrying `U` onto `U'` induces a
symplectomorphism of reduced spaces, compatibly with identities and composition
(`TauCeti.SymplecticForm.reducedSpaceCongr`). Hence a group acting by linear symplectomorphisms
preserving `U` acts by symplectomorphisms on the reduced space
(`TauCeti.SymplecticForm.reducedSpaceRepresentation`).

Reduction also acts on subspaces: the image of `L ∩ U` in the reduced space is isotropic when `L`
is, and for coisotropic `U` it is Lagrangian when `L` is
(`TauCeti.SymplecticForm.IsLagrangian.reduction_map`). This is the linear form of the reduction of
Lagrangian submanifolds by a coisotropic one.

The underlying construction, valid for any alternating real bilinear form `B`, is the symplectic
form on `V ⧸ ker B` (`LinearMap.BilinForm.IsAlt.symplecticFormQuotKer`).

## Main definitions

* `LinearMap.BilinForm.IsAlt.symplecticFormQuotKer`: an alternating form descends to a symplectic
  form on the quotient by its kernel.
* `TauCeti.SymplecticForm.ReducedSpace ω U`: the reduced space `U ⧸ (U ∩ U^ω)`.
* `TauCeti.SymplecticForm.reduction ω U`: its symplectic form `[u], [v] ↦ ω(u, v)`.
* `TauCeti.SymplecticForm.reducedSpaceCongr`: the symplectomorphism of reduced spaces induced by a
  linear symplectomorphism.
* `TauCeti.SymplecticForm.reducedSpaceRepresentation`: the induced symplectic representation of a
  group on a reduced space.

## Main results

* `TauCeti.SymplecticForm.map_subtype_ker_restrict`: the kernel of the restriction of `ω` to `U`
  is `U ∩ U^ω`.
* `TauCeti.SymplecticForm.finrank_reducedSpace_add_finrank_inf`: `dim U_red + dim (U ∩ U^ω) =
  dim U`, and `TauCeti.SymplecticForm.even_finrank_add_finrank_inf`: `dim U + dim (U ∩ U^ω)` is
  even.
* `TauCeti.SymplecticForm.IsCoisotropic.finrank_reducedSpace_add_finrank`: for coisotropic `U`,
  `dim U_red + dim V = 2 dim U`.
* `TauCeti.SymplecticForm.finrank_reducedSpace_orthogonal_add`: `dim (W^ω)_red + dim W +
  dim (W ∩ W^ω) = dim V`.
* `TauCeti.SymplecticForm.subsingleton_reducedSpace_iff`,
  `TauCeti.SymplecticForm.isSymplectomorphism_quotEquivOfEqBot`: the reduced space is trivial
  exactly for isotropic `U`, and is `U` itself with the restricted form for symplectic `U`.
* `TauCeti.SymplecticForm.IsIsotropic.reduction_map`,
  `TauCeti.SymplecticForm.IsLagrangian.reduction_map`: reduction of isotropic and Lagrangian
  subspaces.

## References

* Alan Weinstein, *Lectures on Symplectic Manifolds*, CBMS Regional Conference Series in
  Mathematics 29, American Mathematical Society, 1977 (linear symplectic reduction and the
  reduction of Lagrangian subspaces by a coisotropic subspace).
* Victor Guillemin and Shlomo Sternberg, *Symplectic Techniques in Physics*, Cambridge University
  Press, 1984 (linear reduction; the symplectic normal space in the local normal form of
  Hamiltonian actions).
-/

public section

open Module

namespace LinearMap.BilinForm.IsAlt

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {B : LinearMap.BilinForm ℝ V}

/-- An alternating real bilinear form `B` descends to a symplectic form `[v], [w] ↦ B v w` on the
quotient of `V` by the kernel of `B`. -/
noncomputable def symplecticFormQuotKer (hB : B.IsAlt) :
    TauCeti.SymplecticForm (V ⧸ LinearMap.ker B) :=
  have hAlt : (hB.isRefl.liftQ₂ B (LinearMap.ker B) le_rfl).IsAlt := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H v => exact hB.self_eq_zero v
  { toBilinForm := hB.isRefl.liftQ₂ B (LinearMap.ker B) le_rfl
    isAlt := hAlt
    nondegenerate := by
      refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hAlt.isRefl).mpr fun x hx => ?_
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
        ext w
        exact hx (Submodule.Quotient.mk w) }

/-- The defining formula `[v], [w] ↦ B v w` of the symplectic form on `V ⧸ ker B`. -/
@[simp]
theorem symplecticFormQuotKer_mk (hB : B.IsAlt) (v w : V) :
    hB.symplecticFormQuotKer (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) = B v w :=
  (rfl)

end LinearMap.BilinForm.IsAlt

namespace TauCeti.SymplecticForm

variable {V V' V'' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup V''] [Module ℝ V'']

section Basic

variable (ω : SymplecticForm V) (U : Submodule ℝ V)

/-- A vector of `U` lies in the kernel of the restriction of `ω` to `U` exactly when it lies in
the symplectic complement `U^ω`. -/
theorem mem_ker_restrict_iff {u : U} :
    u ∈ LinearMap.ker (ω.toBilinForm.restrict U) ↔ (u : V) ∈ ω.orthogonal U := by
  rw [LinearMap.mem_ker, mem_orthogonal_iff']
  refine ⟨fun h y hy => ?_, fun h => LinearMap.ext fun y => h y y.2⟩
  simpa using LinearMap.congr_fun h ⟨y, hy⟩

/-- The kernel of the restriction of `ω` to `U`, viewed in `V`, is `U ∩ U^ω`. -/
theorem map_subtype_ker_restrict :
    (LinearMap.ker (ω.toBilinForm.restrict U)).map U.subtype = U ⊓ ω.orthogonal U := by
  ext v
  simp only [Submodule.mem_map, Submodule.mem_inf, mem_ker_restrict_iff, Submodule.subtype_apply]
  exact ⟨fun ⟨u, hu, hv⟩ => hv ▸ ⟨u.2, hu⟩, fun ⟨hv, hv'⟩ => ⟨⟨v, hv⟩, hv', rfl⟩⟩

/-- The **reduced space** `U ⧸ (U ∩ U^ω)` of a subspace `U` of a symplectic vector space: the
quotient of `U` by the kernel of the restriction of `ω`. -/
abbrev ReducedSpace : Type _ :=
  U ⧸ LinearMap.ker (ω.toBilinForm.restrict U)

/-- The **linear symplectic reduction** of `ω` along `U`: the symplectic form
`[u], [v] ↦ ω(u, v)` on the reduced space `U ⧸ (U ∩ U^ω)`. -/
noncomputable def reduction : SymplecticForm (ω.ReducedSpace U) :=
  LinearMap.BilinForm.IsAlt.symplecticFormQuotKer (B := ω.toBilinForm.restrict U) <| by
    intro u
    exact ω.self_eq_zero u

/-- The defining formula `ω_red([u], [v]) = ω(u, v)` of the reduced symplectic form. -/
@[simp]
theorem reduction_mk (u v : U) :
    ω.reduction U (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ω u v :=
  (rfl)

variable {ω U} in
/-- Two vectors of `U` have the same class in the reduced space exactly when they differ by an
element of `U^ω`. -/
theorem ReducedSpace.mk_eq_mk_iff {u v : U} :
    (Submodule.Quotient.mk u : ω.ReducedSpace U) = Submodule.Quotient.mk v ↔
      (u : V) - v ∈ ω.orthogonal U := by
  rw [Submodule.Quotient.eq, mem_ker_restrict_iff, Submodule.coe_sub]

/-- The reduced space is trivial exactly when `U` is isotropic. -/
theorem subsingleton_reducedSpace_iff :
    Subsingleton (ω.ReducedSpace U) ↔ ω.IsIsotropic U := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff', isIsotropic_iff_le]
  exact ⟨fun h u hu => (mem_ker_restrict_iff ω U).1 (h ⟨u, hu⟩),
    fun h u => (mem_ker_restrict_iff ω U).2 (h u.2)⟩

/-- The kernel of the restriction of `ω` to `U` is trivial exactly when `U` is a symplectic
subspace. -/
theorem ker_restrict_eq_bot_iff :
    LinearMap.ker (ω.toBilinForm.restrict U) = ⊥ ↔ ω.IsSymplectic U := by
  rw [isSymplectic_iff_disjoint, Submodule.disjoint_def, Submodule.eq_bot_iff]
  refine ⟨fun h v hv hv' => ?_,
    fun h u hu => Subtype.ext <| h u u.2 ((mem_ker_restrict_iff ω U).1 hu)⟩
  simpa using h ⟨v, hv⟩ ((mem_ker_restrict_iff ω U).2 hv')

/-- For a symplectic subspace `U`, there is nothing to divide out: the identification of the
reduced space with `U` is a symplectomorphism onto the restriction of `ω` to `U`. -/
theorem isSymplectomorphism_quotEquivOfEqBot (h : ω.IsSymplectic U) :
    IsSymplectomorphism (ω.reduction U) (ω.restrict U h.nondegenerate_restrict)
      (Submodule.quotEquivOfEqBot _ ((ker_restrict_eq_bot_iff ω U).2 h)) := by
  rw [isSymplectomorphism_iff]
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H u =>
  induction y using Submodule.Quotient.induction_on with
  | H v => simp

end Basic

section Finrank

variable (ω : SymplecticForm V) (U : Submodule ℝ V)

/-- The dimension count of linear reduction: `dim (U ⧸ (U ∩ U^ω)) + dim (U ∩ U^ω) = dim U`. -/
theorem finrank_reducedSpace_add_finrank_inf [FiniteDimensional ℝ U] :
    finrank ℝ (ω.ReducedSpace U) + finrank ℝ ↥(U ⊓ ω.orthogonal U) = finrank ℝ U := by
  rw [← map_subtype_ker_restrict, Submodule.finrank_map_subtype_eq,
    Submodule.finrank_quotient_add_finrank]

/-- The restriction of a symplectic form to a subspace `U` has even rank: `dim U + dim (U ∩ U^ω)`
is even. -/
theorem even_finrank_add_finrank_inf [FiniteDimensional ℝ U] :
    Even (finrank ℝ U + finrank ℝ ↥(U ⊓ ω.orthogonal U)) := by
  obtain ⟨k, hk⟩ := (ω.reduction U).even_finrank
  refine ⟨k + finrank ℝ ↥(U ⊓ ω.orthogonal U), ?_⟩
  have := finrank_reducedSpace_add_finrank_inf ω U
  omega

/-- The reduced space of a coisotropic subspace `U` is `U ⧸ U^ω`, of dimension
`2 dim U - dim V`. -/
theorem IsCoisotropic.finrank_reducedSpace_add_finrank [FiniteDimensional ℝ V]
    {ω : SymplecticForm V} {U : Submodule ℝ V} (h : ω.IsCoisotropic U) :
    finrank ℝ (ω.ReducedSpace U) + finrank ℝ V = 2 * finrank ℝ U := by
  have h₁ := finrank_reducedSpace_add_finrank_inf ω U
  rw [inf_eq_right.2 (isCoisotropic_iff_le.1 h)] at h₁
  have h₂ := ω.finrank_add_finrank_orthogonal U
  omega

/-- The symplectic normal space `W^ω ⧸ (W ∩ W^ω)` of a subspace `W` has dimension
`dim V - dim W - dim (W ∩ W^ω)`: the radical of `ω` on `W^ω` is again `W ∩ W^ω`. -/
theorem finrank_reducedSpace_orthogonal_add [FiniteDimensional ℝ V] (W : Submodule ℝ V) :
    finrank ℝ (ω.ReducedSpace (ω.orthogonal W)) + finrank ℝ W +
      finrank ℝ ↥(W ⊓ ω.orthogonal W) = finrank ℝ V := by
  have h₁ := finrank_reducedSpace_add_finrank_inf ω (ω.orthogonal W)
  rw [orthogonal_orthogonal, inf_comm] at h₁
  have h₂ := ω.finrank_add_finrank_orthogonal W
  omega

end Finrank

section Functoriality

variable {ω : SymplecticForm V} {ω' : SymplecticForm V'} {ω'' : SymplecticForm V''}

/-- The linear equivalence `U ≃ U'` induced by `e` maps the kernel of the restriction of `ω` to
`U` onto that of `ω'` on `U'`. -/
private theorem map_ker_restrict_congr {e : V ≃ₗ[ℝ] V'} (he : IsSymplectomorphism ω ω' e)
    {U : Submodule ℝ V} {U' : Submodule ℝ V'} (hU : U.map (e : V →ₗ[ℝ] V') = U') :
    (LinearMap.ker (ω.toBilinForm.restrict U)).map
        (((e.submoduleMap U).trans (LinearEquiv.ofEq _ _ hU) : U ≃ₗ[ℝ] U') : U →ₗ[ℝ] U') =
      LinearMap.ker (ω'.toBilinForm.restrict U') := by
  subst hU
  ext y
  rw [Submodule.mem_map_equiv, mem_ker_restrict_iff, mem_ker_restrict_iff,
    ← he.map_orthogonal U, Submodule.mem_map_equiv]
  simp [LinearEquiv.submoduleMap_symm_apply]

variable (ω ω') in
/-- A linear symplectomorphism `e : V ≃ V'` carrying `U` onto `U'` induces the linear equivalence
`[u] ↦ [e u]` of reduced spaces; it is a symplectomorphism
(`TauCeti.SymplecticForm.isSymplectomorphism_reducedSpaceCongr`). -/
noncomputable def reducedSpaceCongr (e : V ≃ₗ[ℝ] V') (he : IsSymplectomorphism ω ω' e)
    {U : Submodule ℝ V} {U' : Submodule ℝ V'} (hU : U.map (e : V →ₗ[ℝ] V') = U') :
    ω.ReducedSpace U ≃ₗ[ℝ] ω'.ReducedSpace U' :=
  Submodule.Quotient.equiv _ _ ((e.submoduleMap U).trans (LinearEquiv.ofEq _ _ hU))
    (map_ker_restrict_congr he hU)

/-- The induced map of reduced spaces is `[u] ↦ [e u]`. -/
@[simp]
theorem reducedSpaceCongr_mk (e : V ≃ₗ[ℝ] V') (he : IsSymplectomorphism ω ω' e)
    {U : Submodule ℝ V} {U' : Submodule ℝ V'} (hU : U.map (e : V →ₗ[ℝ] V') = U') (u : U) :
    reducedSpaceCongr ω ω' e he hU (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨e u, hU ▸ Submodule.mem_map_of_mem u.2⟩ :=
  (rfl)

/-- The map of reduced spaces induced by a linear symplectomorphism is a symplectomorphism. -/
theorem isSymplectomorphism_reducedSpaceCongr (e : V ≃ₗ[ℝ] V')
    (he : IsSymplectomorphism ω ω' e) {U : Submodule ℝ V} {U' : Submodule ℝ V'}
    (hU : U.map (e : V →ₗ[ℝ] V') = U') :
    IsSymplectomorphism (ω.reduction U) (ω'.reduction U') (reducedSpaceCongr ω ω' e he hU) := by
  rw [isSymplectomorphism_iff]
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H u =>
  induction y using Submodule.Quotient.induction_on with
  | H v => simpa using he.apply u v

/-- The identity induces the identity of reduced spaces. -/
@[simp]
theorem reducedSpaceCongr_refl {U : Submodule ℝ V}
    (hU : U.map (LinearEquiv.refl ℝ V : V →ₗ[ℝ] V) = U) :
    reducedSpaceCongr ω ω (LinearEquiv.refl ℝ V) (IsSymplectomorphism.refl ω) hU =
      LinearEquiv.refl ℝ _ := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H u => simp

/-- The map of reduced spaces induced by a composite is the composite of the induced maps. -/
theorem reducedSpaceCongr_trans {e : V ≃ₗ[ℝ] V'} {f : V' ≃ₗ[ℝ] V''}
    (he : IsSymplectomorphism ω ω' e) (hf : IsSymplectomorphism ω' ω'' f) {U : Submodule ℝ V}
    {U' : Submodule ℝ V'} {U'' : Submodule ℝ V''} (hU : U.map (e : V →ₗ[ℝ] V') = U')
    (hU' : U'.map (f : V' →ₗ[ℝ] V'') = U'')
    (hU'' : U.map ((e.trans f : V ≃ₗ[ℝ] V'') : V →ₗ[ℝ] V'') = U'') :
    reducedSpaceCongr ω ω'' (e.trans f) (he.trans hf) hU'' =
      (reducedSpaceCongr ω ω' e he hU).trans (reducedSpaceCongr ω' ω'' f hf hU') := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H u => simp

/-- The map of reduced spaces induced by an inverse is the inverse of the induced map. -/
theorem reducedSpaceCongr_symm {e : V ≃ₗ[ℝ] V'} (he : IsSymplectomorphism ω ω' e)
    {U : Submodule ℝ V} {U' : Submodule ℝ V'} (hU : U.map (e : V →ₗ[ℝ] V') = U')
    (hU' : U'.map (e.symm : V' →ₗ[ℝ] V) = U) :
    reducedSpaceCongr ω' ω e.symm he.symm hU' = (reducedSpaceCongr ω ω' e he hU).symm := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [LinearEquiv.eq_symm_apply, reducedSpaceCongr_mk, reducedSpaceCongr_mk]
    congr 1
    ext
    simp

variable (ω) in
/-- A group acting on `V` by linear symplectomorphisms that preserve `U` acts by
symplectomorphisms on the reduced space `U ⧸ (U ∩ U^ω)`
(`TauCeti.SymplecticForm.isSymplectomorphism_reducedSpaceRepresentation`), by `[u] ↦ [g u]`. -/
noncomputable def reducedSpaceRepresentation {G : Type*} [Group G] (ρ : G →* V ≃ₗ[ℝ] V)
    (hρ : ∀ g, IsSymplectomorphism ω ω (ρ g)) (U : Submodule ℝ V) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    G →* ω.ReducedSpace U ≃ₗ[ℝ] ω.ReducedSpace U :=
  have hmap (g : G) : U.map (ρ g : V →ₗ[ℝ] V) = U := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun u hu => hU g u hu) fun u hu => ?_
    refine ⟨ρ g⁻¹ u, hU g⁻¹ u hu, ?_⟩
    simp
  { toFun g := reducedSpaceCongr ω ω (ρ g) (hρ g) (hmap g)
    map_one' := by
      ext x
      induction x using Submodule.Quotient.induction_on with
      | H u => simp
    map_mul' g h := by
      ext x
      induction x using Submodule.Quotient.induction_on with
      | H u => simp }

/-- The induced action on the reduced space is `[u] ↦ [g u]`. -/
@[simp]
theorem reducedSpaceRepresentation_apply_mk {G : Type*} [Group G] (ρ : G →* V ≃ₗ[ℝ] V)
    (hρ : ∀ g, IsSymplectomorphism ω ω (ρ g)) (U : Submodule ℝ V) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U)
    (g : G) (u : U) :
    ω.reducedSpaceRepresentation ρ hρ U hU g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨ρ g u, hU g u u.2⟩ :=
  (rfl)

/-- A group acting by linear symplectomorphisms preserving `U` acts by symplectomorphisms of the
reduced space. -/
theorem isSymplectomorphism_reducedSpaceRepresentation {G : Type*} [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (hρ : ∀ g, IsSymplectomorphism ω ω (ρ g)) (U : Submodule ℝ V)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (g : G) :
    IsSymplectomorphism (ω.reduction U) (ω.reduction U)
      (ω.reducedSpaceRepresentation ρ hρ U hU g) :=
  isSymplectomorphism_reducedSpaceCongr _ (hρ g) _

end Functoriality

section Subspaces

variable {ω : SymplecticForm V} {U L : Submodule ℝ V}

/-- The image in the reduced space of `L ∩ U`, for an isotropic subspace `L`, is isotropic. -/
theorem IsIsotropic.reduction_map (hL : ω.IsIsotropic L) :
    (ω.reduction U).IsIsotropic
      ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ) := by
  rw [isIsotropic_iff]
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  exact (isIsotropic_iff.1 hL) u hu v hv

/-- **Reduction of Lagrangian subspaces.** For a coisotropic subspace `U` and a Lagrangian
subspace `L`, the image of `L ∩ U` in the reduced space `U ⧸ U^ω` is Lagrangian. -/
theorem IsLagrangian.reduction_map [FiniteDimensional ℝ V] (hL : ω.IsLagrangian L)
    (hU : ω.IsCoisotropic U) :
    (ω.reduction U).IsLagrangian
      ((L.comap U.subtype).map (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ) := by
  refine isLagrangian_iff.2 ⟨hL.isIsotropic.reduction_map, ?_⟩
  rw [isCoisotropic_iff]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H u =>
  -- `u` is `ω`-orthogonal to `L ∩ U`, hence lies in `(L ∩ U)^ω = L + U^ω`.
  have hu : (u : V) ∈ ω.orthogonal (L ⊓ U) := by
    rw [mem_orthogonal_iff']
    intro y hy
    simpa using (mem_orthogonal_iff'.1 hx) (Submodule.Quotient.mk ⟨y, hy.2⟩)
      ⟨⟨y, hy.2⟩, hy.1, rfl⟩
  rw [orthogonal_inf, le_antisymm (isCoisotropic_iff_le.1 hL.isCoisotropic)
    (isIsotropic_iff_le.1 hL.isIsotropic)] at hu
  obtain ⟨l, hl, c, hc, hlc⟩ := Submodule.mem_sup.1 hu
  -- Since `U^ω ⊆ U`, the `L`-component `l = u - c` lies in `L ∩ U` and has the class of `u`.
  have hlU : l ∈ U := by
    have : l = u - c := by rw [← hlc]; abel
    exact this ▸ U.sub_mem u.2 (isCoisotropic_iff_le.1 hU hc)
  refine ⟨⟨l, hlU⟩, hl, ReducedSpace.mk_eq_mk_iff.2 ?_⟩
  have : l - (u : V) = -c := by rw [← hlc]; abel
  exact this ▸ (ω.orthogonal U).neg_mem hc

end Subspaces

end TauCeti.SymplecticForm
