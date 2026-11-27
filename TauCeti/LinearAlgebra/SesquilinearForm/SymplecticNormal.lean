/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Quotient.Bilinear
import TauCeti.Algebra.Module.Submodule.Map
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Symplectic normal spaces of forms with values in a module

Let `B : V → V → Q` be a reflexive bilinear map with values in a module `Q`, and let `W` be a
subspace of `V`. Its orthogonal `W^⊥ = {v | ∀ w ∈ W, B w v = 0}` is `Submodule.orthogonalBilin`.
The **symplectic normal space** of `W` is the quotient `W^⊥ ⧸ (W ∩ W^⊥)`
(`LinearMap.SymplecticNormal B W`). Since `B` is reflexive, it descends to a `Q`-valued form on
this quotient, `[u], [v] ↦ B u v` (`LinearMap.IsRefl.symplecticNormalForm`), alternating when `B`
is. For an isotropic subspace, `W ≤ W^⊥`, this is the quotient `W^⊥ ⧸ W`.

The main case is that of a line: `Q` is one-dimensional and `B` is nondegenerate, in the sense
that `v ↦ B v` is injective. This is the shape of the Levi form `ξ × ξ → TM ⧸ ξ` of a contact
structure, whose values lie in the contact line rather than in the scalars. Then:

* the induced form on the symplectic normal space is again nondegenerate
  (`LinearMap.IsRefl.injective_symplecticNormalForm`), and identifying `Q` with the scalars by any
  nonzero functional makes it a nondegenerate bilinear form
  (`LinearMap.IsRefl.nondegenerate_compr₂_symplecticNormalForm`);
* for every `W`, `dim (W^⊥ ⧸ (W ∩ W^⊥)) + dim (W ∩ W^⊥) + dim W = dim V`
  (`LinearMap.finrank_symplecticNormal_add_finrank_inf_add_finrank`); for an isotropic `W` this
  reads `dim (W^⊥ ⧸ W) + 2 dim W = dim V`
  (`LinearMap.finrank_symplecticNormal_add_two_mul_finrank`), so the symplectic normal space is
  zero exactly when `W` has half the dimension of `V`
  (`LinearMap.subsingleton_symplecticNormal_iff`).

The construction is functorial. A linear equivalence `e : V ≃ V'` carrying `W` onto `W'` and `B`
to `B'` up to an injective linear map `eQ : Q → Q'` of the value modules,
`B' (e u) (e v) = eQ (B u v)`, carries orthogonals to orthogonals
(`LinearEquiv.map_orthogonalBilin`), so it induces the linear equivalence `[u] ↦ [e u]` of
symplectic normal spaces (`LinearMap.symplecticNormalCongr`), which carries the induced form of `B`
to that of `B'` up to `eQ` (`LinearMap.IsRefl.symplecticNormalForm_symplecticNormalCongr`) and is
compatible with identities, composition and inverses.

For a scalar-valued symplectic form `ω` the same quotient appears in linear reduction as the
reduced space `TauCeti.SymplecticForm.ReducedSpace ω (ω.orthogonal W)`, written there as the
quotient of `W^ω` by the kernel of the restricted form. The module-valued version is the one
needed for the conformal symplectic normal spaces of isotropic submanifolds of contact manifolds,
whose Levi form takes values in the contact line: a contact structure need not have a global
defining form.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle of an isotropic submanifold).
* A. Weinstein, *Neighborhood classification of isotropic embeddings*, Journal of Differential
  Geometry 16 (1981), 125–128 (the symplectic normal bundle `TN^ω ⧸ TN` of an isotropic
  submanifold).
-/

public section

noncomputable section

open Module

namespace LinearMap

section CommRing

variable {K V Q : Type*} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup Q] [Module K Q]
  {B : V →ₗ[K] V →ₗ[K] Q} {W : Submodule K V}

variable (B W) in
/-- The **symplectic normal space** `W^⊥ ⧸ (W ∩ W^⊥)` of a subspace `W` for a bilinear map `B`,
where `W^⊥ = {v | ∀ w ∈ W, B w v = 0}` is the orthogonal `Submodule.orthogonalBilin`. For an
isotropic `W` this is `W^⊥ ⧸ W`. -/
abbrev SymplecticNormal : Type _ :=
  W.orthogonalBilin B ⧸ W.comap (W.orthogonalBilin B).subtype

/-- The intersection of `W` with its orthogonal pairs to zero with the whole orthogonal: this is
what lets a reflexive form descend to the symplectic normal space. -/
private theorem comap_le_ker_domRestrict₁₂ :
    W.comap (W.orthogonalBilin B).subtype ≤
      LinearMap.ker (B.domRestrict₁₂ (W.orthogonalBilin B) (W.orthogonalBilin B)) :=
  fun w hw ↦ LinearMap.mem_ker.2 <| LinearMap.ext fun u ↦ u.property w hw

variable (W) in
/-- The form `[u], [v] ↦ B u v` induced by a reflexive bilinear map `B` on the symplectic normal
space `W^⊥ ⧸ (W ∩ W^⊥)` of a subspace `W`. -/
def IsRefl.symplecticNormalForm (hB : B.IsRefl) :
    SymplecticNormal B W →ₗ[K] SymplecticNormal B W →ₗ[K] Q :=
  IsRefl.liftQ₂ (B.domRestrict₁₂ _ _) _ (hB.domRestrict _) comap_le_ker_domRestrict₁₂

/-- The defining formula `[u], [v] ↦ B u v` of the form on the symplectic normal space. -/
@[simp]
theorem IsRefl.symplecticNormalForm_mk (hB : B.IsRefl) (u v : W.orthogonalBilin B) :
    hB.symplecticNormalForm W (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = B u v :=
  (rfl)

/-- The form induced on the symplectic normal space by a reflexive form is reflexive. -/
theorem IsRefl.isRefl_symplecticNormalForm (hB : B.IsRefl) :
    (hB.symplecticNormalForm W).IsRefl := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    induction y using Submodule.Quotient.induction_on with
    | H v => exact hB u v

/-- The form induced on the symplectic normal space by an alternating form is alternating. -/
theorem IsAlt.isAlt_symplecticNormalForm (hB : B.IsAlt) :
    (hB.isRefl.symplecticNormalForm W).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H u => simpa using hB u

/-! ### Functoriality -/

section Congr

variable {V' Q' V'' Q'' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup Q'] [Module K Q']
  [AddCommGroup V''] [Module K V''] [AddCommGroup Q''] [Module K Q'']
  {B' : V' →ₗ[K] V' →ₗ[K] Q'} {B'' : V'' →ₗ[K] V'' →ₗ[K] Q''} {W' : Submodule K V'}
  {W'' : Submodule K V''}

/-- **Orthogonals are natural.** A linear equivalence `e : V ≃ V'` that carries `B` to `B'` up
to an injective linear map `eQ` of the value modules, `B' (e u) (e v) = eQ (B u v)`, carries the
orthogonal of `W` for `B` onto the orthogonal of `e(W)` for `B'`. -/
theorem _root_.LinearEquiv.map_orthogonalBilin (e : V ≃ₗ[K] V') {eQ : Q →ₗ[K] Q'}
    (heQ : Function.Injective eQ) (he : ∀ u v, B' (e u) (e v) = eQ (B u v))
    (W : Submodule K V) :
    (W.orthogonalBilin B).map (e : V →ₗ[K] V') = (W.map (e : V →ₗ[K] V')).orthogonalBilin B' := by
  ext y
  obtain ⟨v, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_orthogonalBilin,
    Submodule.mem_orthogonalBilin]
  refine ⟨fun h _ hw' ↦ ?_, fun h w hw ↦ heQ ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hw'
    rw [LinearEquiv.coe_coe, he, h w hw, map_zero]
  · rw [← he, map_zero]
    exact h _ (Submodule.mem_map_of_mem hw)

variable (B B') in
/-- A linear equivalence `e : V ≃ V'` carrying `W` onto `W'` and the orthogonal `W^⊥` of `W` for
`B` onto the orthogonal `W'^⊥` of `W'` for `B'` induces the linear equivalence `[u] ↦ [e u]` of
symplectic normal spaces `W^⊥ ⧸ (W ∩ W^⊥) ≃ W'^⊥ ⧸ (W' ∩ W'^⊥)`. When `e` carries `B` to `B'` up
to an injective map of the value modules, the second condition follows from the first
(`LinearEquiv.map_orthogonalBilin`), and the equivalence carries the induced forms to each other
(`LinearMap.IsRefl.symplecticNormalForm_symplecticNormalCongr`). -/
def symplecticNormalCongr (e : V ≃ₗ[K] V') (hW : W.map (e : V →ₗ[K] V') = W')
    (hWB : (W.orthogonalBilin B).map (e : V →ₗ[K] V') = W'.orthogonalBilin B') :
    SymplecticNormal B W ≃ₗ[K] SymplecticNormal B' W' :=
  Submodule.Quotient.equiv _ _ (e.ofSubmodules _ _ hWB) (e.map_comap_subtype_ofSubmodules hWB hW)

/-- The induced map of symplectic normal spaces is `[u] ↦ [e u]`. -/
@[simp]
theorem symplecticNormalCongr_mk (e : V ≃ₗ[K] V') (hW : W.map (e : V →ₗ[K] V') = W')
    (hWB : (W.orthogonalBilin B).map (e : V →ₗ[K] V') = W'.orthogonalBilin B')
    (u : W.orthogonalBilin B) :
    symplecticNormalCongr B B' e hW hWB (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨e u, hWB ▸ Submodule.mem_map_of_mem u.property⟩ :=
  (rfl)

/-- **The induced map of symplectic normal spaces is conformal.** If `e` carries `B` to `B'` up to
the linear map `eQ` of the value modules, `B' (e u) (e v) = eQ (B u v)`, then the induced map of
symplectic normal spaces carries the induced form of `B` to that of `B'` up to `eQ`. -/
theorem IsRefl.symplecticNormalForm_symplecticNormalCongr (hB : B.IsRefl) (hB' : B'.IsRefl)
    {e : V ≃ₗ[K] V'} {eQ : Q →ₗ[K] Q'} (he : ∀ u v, B' (e u) (e v) = eQ (B u v))
    (hW : W.map (e : V →ₗ[K] V') = W')
    (hWB : (W.orthogonalBilin B).map (e : V →ₗ[K] V') = W'.orthogonalBilin B')
    (x y : SymplecticNormal B W) :
    hB'.symplecticNormalForm W' (symplecticNormalCongr B B' e hW hWB x)
        (symplecticNormalCongr B B' e hW hWB y) =
      eQ (hB.symplecticNormalForm W x y) := by
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    induction y using Submodule.Quotient.induction_on with
    | H v => simp [he]

/-- The identity induces the identity of symplectic normal spaces. -/
@[simp]
theorem symplecticNormalCongr_refl (hW : W.map (LinearEquiv.refl K V : V →ₗ[K] V) = W)
    (hWB : (W.orthogonalBilin B).map (LinearEquiv.refl K V : V →ₗ[K] V) = W.orthogonalBilin B) :
    symplecticNormalCongr B B (LinearEquiv.refl K V) hW hWB = LinearEquiv.refl K _ := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H u => simp

/-- The map of symplectic normal spaces induced by a composite is the composite of the induced
maps. -/
theorem symplecticNormalCongr_trans {e : V ≃ₗ[K] V'} {e' : V' ≃ₗ[K] V''}
    (hW : W.map (e : V →ₗ[K] V') = W')
    (hWB : (W.orthogonalBilin B).map (e : V →ₗ[K] V') = W'.orthogonalBilin B')
    (hW' : W'.map (e' : V' →ₗ[K] V'') = W'')
    (hWB' : (W'.orthogonalBilin B').map (e' : V' →ₗ[K] V'') = W''.orthogonalBilin B'')
    (hW'' : W.map ((e.trans e' : V ≃ₗ[K] V'') : V →ₗ[K] V'') = W'')
    (hWB'' : (W.orthogonalBilin B).map ((e.trans e' : V ≃ₗ[K] V'') : V →ₗ[K] V'') =
      W''.orthogonalBilin B'') :
    symplecticNormalCongr B B'' (e.trans e') hW'' hWB'' =
      (symplecticNormalCongr B B' e hW hWB).trans (symplecticNormalCongr B' B'' e' hW' hWB') := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H u => simp

/-- The map of symplectic normal spaces induced by an inverse is the inverse of the induced
map. -/
theorem symplecticNormalCongr_symm {e : V ≃ₗ[K] V'} (hW : W.map (e : V →ₗ[K] V') = W')
    (hWB : (W.orthogonalBilin B).map (e : V →ₗ[K] V') = W'.orthogonalBilin B')
    (hW' : W'.map (e.symm : V' →ₗ[K] V) = W)
    (hWB' : (W'.orthogonalBilin B').map (e.symm : V' →ₗ[K] V) = W.orthogonalBilin B) :
    symplecticNormalCongr B' B e.symm hW' hWB' = (symplecticNormalCongr B B' e hW hWB).symm := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [LinearEquiv.eq_symm_apply, symplecticNormalCongr_mk, symplecticNormalCongr_mk]
    congr 1
    ext
    simp

end Congr

end CommRing

section Field

variable {K V Q : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] {B : V →ₗ[K] V →ₗ[K] Q} {W : Submodule K V}

/-- **The induced form on the symplectic normal space is nondegenerate.** If the reflexive
bilinear map `B : V → Hom(V, Q)` is injective and `Q` is one-dimensional, then so is the induced
map on the symplectic normal space of any subspace `W`. -/
theorem IsRefl.injective_symplecticNormalForm (hB : B.IsRefl) (hinj : Function.Injective B)
    (hQ : finrank K Q = 1) : Function.Injective (hB.symplecticNormalForm W) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    -- `u` pairs to zero with `W^⊥`, so it lies in `W^⊥⊥ = W`.
    have hu : (u : V) ∈ (W.orthogonalBilin B).orthogonalBilin B := fun v hv ↦ by
      have := LinearMap.congr_fun hx (Submodule.Quotient.mk ⟨v, hv⟩)
      simp only [symplecticNormalForm_mk] at this
      exact hB _ _ this
    rw [hB.orthogonalBilin_orthogonalBilin_of_injective hinj hQ W] at hu
    simpa using hu

/-- **Identifying the line with the scalars gives a nondegenerate form.** If the reflexive
bilinear map `B : V → Hom(V, Q)` is injective, `Q` is one-dimensional and `e : Q → K` is injective,
then `[u], [v] ↦ e (B u v)` is a nondegenerate bilinear form on the symplectic normal space of any
subspace `W`. -/
theorem IsRefl.nondegenerate_compr₂_symplecticNormalForm (hB : B.IsRefl)
    (hinj : Function.Injective B) (hQ : finrank K Q = 1) {e : Q →ₗ[K] K}
    (he : Function.Injective e) :
    BilinForm.Nondegenerate ((hB.symplecticNormalForm W).compr₂ e) := by
  refine (IsRefl.nondegenerate_iff_separatingLeft
    (hB.isRefl_symplecticNormalForm.compr₂_of_injective he)).2 fun x hx ↦
    hB.injective_symplecticNormalForm hinj hQ ?_
  rw [map_zero]
  ext y
  exact he (by simpa using hx (Submodule.Quotient.mk y))

variable (W) in
/-- **Dimension of the symplectic normal space.** If the bilinear map `B : V → Hom(V, Q)` is
injective and `Q` is one-dimensional, then for every subspace `W`,
`dim (W^⊥ ⧸ (W ∩ W^⊥)) + dim (W ∩ W^⊥) + dim W = dim V`. -/
theorem finrank_symplecticNormal_add_finrank_inf_add_finrank (hinj : Function.Injective B)
    (hQ : finrank K Q = 1) :
    finrank K (SymplecticNormal B W) + finrank K ↥(W ⊓ W.orthogonalBilin B) + finrank K W =
      finrank K V := by
  obtain ⟨e, hnd⟩ := exists_nondegenerate_compr₂_of_injective hinj hQ
  have horth := BilinForm.finrank_orthogonal hnd W
  rw [BilinForm.orthogonal, Submodule.orthogonalBilin_compr₂_of_injective e.injective] at horth
  have hquot : finrank K (SymplecticNormal B W) +
      finrank K (W.comap (W.orthogonalBilin B).subtype) = finrank K (W.orthogonalBilin B) :=
    Submodule.finrank_quotient_add_finrank _
  rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm] at hquot
  have hle := Submodule.finrank_le W
  omega

/-- **Dimension of the symplectic normal space of an isotropic subspace.** If the bilinear map
`B : V → Hom(V, Q)` is injective, `Q` is one-dimensional and `W` is isotropic, then
`dim (W^⊥ ⧸ W) + 2 dim W = dim V`. -/
theorem finrank_symplecticNormal_add_two_mul_finrank (hinj : Function.Injective B)
    (hQ : finrank K Q = 1) (hW : W ≤ W.orthogonalBilin B) :
    finrank K (SymplecticNormal B W) + 2 * finrank K W = finrank K V := by
  have := finrank_symplecticNormal_add_finrank_inf_add_finrank W hinj hQ
  rw [inf_eq_left.2 hW] at this
  omega

/-- **The symplectic normal space of a half-dimensional isotropic subspace is zero.** If the
bilinear map `B : V → Hom(V, Q)` is injective, `Q` is one-dimensional and `W` is isotropic,
then the symplectic normal space `W^⊥ ⧸ W` is zero exactly when
`2 dim W = dim V`. -/
theorem subsingleton_symplecticNormal_iff (hinj : Function.Injective B) (hQ : finrank K Q = 1)
    (hW : W ≤ W.orthogonalBilin B) :
    Subsingleton (SymplecticNormal B W) ↔ 2 * finrank K W = finrank K V := by
  rw [← finrank_zero_iff (R := K), ← finrank_symplecticNormal_add_two_mul_finrank hinj hQ hW]
  omega

end Field

end LinearMap
