/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Prod
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective
import TauCeti.LinearAlgebra.Exact

/-!
# Orientations of short exact sequences

Let `0 → U → V → W → 0` be a short exact sequence of finite-dimensional vector spaces over a
linearly ordered field, with maps `f : U → V` and `g : V → W`. Orientations of `U` and of `W`
orient `V`, **subspace first** (`Orientation.shortExact`): if `u₁, …, uₐ` is a positive basis of
`U` and `v₁, …, v_c` are lifts along `g` of a positive basis of `W`, then
`f u₁, …, f uₐ, v₁, …, v_c` is a positive basis of `V` (`Orientation.shortExact_basis_orientation`).
The orientation does not depend on the lifts: it is the transport of the product orientation along
the splitting `(u, w) ↦ f u + s w` for any linear section `s` of `g`
(`Orientation.shortExact_eq_map_prod`).

Conversely, orientations of `V` and `W` determine a unique orientation of `U`
(`Orientation.shortExactLeft`), characterized by `Orientation.shortExactLeft_eq_iff`. This is how
the orientation of a submanifold is induced from an orientation of the ambient space and of its
normal space, as in the orientation of transverse intersections and fibre products
(`TauCeti.LinearAlgebra.Orientation.FiberProduct`) and of spaces of gradient trajectories in Morse
homology. The construction is natural for isomorphisms of short exact sequences
(`Orientation.map_shortExact`), and reversing either outer orientation reverses the middle one.

This is the orientation counterpart of the determinant-line isomorphism
`TauCeti.detLineShortExactEquiv`, which uses the same subspace-first order.

## Main definitions

* `Orientation.shortExact`: the orientation of `V` induced by orientations of `U` and `W`.
* `Orientation.shortExactLeft`: the orientation of `U` induced by orientations of `V` and `W`.

## Main results

* `Orientation.shortExact_eq_map_prod`: the induced orientation is the product orientation
  transported along the splitting given by any section.
* `Orientation.shortExact_basis_orientation`: a basis of `V` made of the image of a basis of `U`
  followed by lifts of a basis of `W` has the induced orientation.
* `Orientation.map_shortExact`: naturality for isomorphisms of short exact sequences.
* `Orientation.shortExact_inj_left`, `Orientation.shortExact_inj_right`: the induced orientation
  determines each outer orientation given the other.
* `Orientation.shortExactLeft_eq_iff`: the characterization of `Orientation.shortExactLeft`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section
noncomputable section

open Module

namespace Orientation

variable {K U V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {f : U →ₗ[K] V} {g : V →ₗ[K] W} {a c : ℕ}

/-! ### Splittings -/

/-- The splitting `U × W ≃ V`, `(u, w) ↦ f u + s w`, of a short exact sequence along a section
`s` of `g`. -/
private def splitEquiv (hf : Function.Injective f) (hfg : Function.Exact f g) (s : W →ₗ[K] V)
    (hs : g ∘ₗ s = LinearMap.id) : (U × W) ≃ₗ[K] V :=
  (hfg.splitSurjectiveEquiv hf ⟨s, hs⟩).1.symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem splitEquiv_apply (hf : Function.Injective f) (hfg : Function.Exact f g)
    (s : W →ₗ[K] V) (hs : g ∘ₗ s = LinearMap.id) (x : U × W) :
    splitEquiv hf hfg s hs x = f x.1 + s x.2 :=
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem exists_section (hg : Function.Surjective g) :
    ∃ s : W →ₗ[K] V, g ∘ₗ s = LinearMap.id :=
  g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)

/-- The splittings along two sections `s` and `s'` differ by an automorphism of `U × W` of
positive determinant: it is the block triangular map `(u, w) ↦ (u + φ w, w)`, where
`f ∘ φ = s - s'`, so its determinant is `1` (`LinearEquiv.det_skewProd`). -/
private theorem det_splitEquiv_trans_symm_pos [FiniteDimensional K U] [FiniteDimensional K W]
    (hf : Function.Injective f) (hfg : Function.Exact f g) {s s' : W →ₗ[K] V}
    (hs : g ∘ₗ s = LinearMap.id) (hs' : g ∘ₗ s' = LinearMap.id) :
    0 < LinearMap.det
      ((splitEquiv hf hfg s hs).trans (splitEquiv hf hfg s' hs').symm : (U × W) →ₗ[K] U × W) := by
  -- `s - s'` takes values in `ker g = range f`, so it lifts along `f` through a retraction `r`.
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  have hgs (w : W) : g (s w) = w := LinearMap.congr_fun hs w
  have hgs' (w : W) : g (s' w) = w := LinearMap.congr_fun hs' w
  have hφ (w : W) : f (r (s w - s' w)) = s w - s' w := by
    obtain ⟨u, hu⟩ := (hfg (s w - s' w)).1 (by rw [map_sub, hgs, hgs', sub_self])
    rw [← hu, ← LinearMap.comp_apply r f, hr, LinearMap.id_apply]
  set σ : (U × W) ≃ₗ[K] U × W := ((LinearEquiv.prodComm K W U).symm.trans
    ((LinearEquiv.refl K W).skewProd (LinearEquiv.refl K U) (r ∘ₗ (s - s')))).trans
      (LinearEquiv.prodComm K W U)
  have hσ : (splitEquiv hf hfg s hs).trans (splitEquiv hf hfg s' hs').symm = σ := by
    ext1 x
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
    simp only [σ, splitEquiv_apply, LinearEquiv.trans_apply, LinearEquiv.symm_prodComm,
      LinearEquiv.prodComm_apply, LinearEquiv.skewProd_apply, LinearEquiv.refl_apply,
      Prod.fst_swap, Prod.snd_swap, LinearMap.comp_apply, LinearMap.sub_apply, map_add, hφ]
    abel
  rw [hσ, ← LinearEquiv.coe_det, LinearEquiv.det_conj, LinearEquiv.det_skewProd]
  simp

private theorem map_splitEquiv_eq [FiniteDimensional K U] [FiniteDimensional K W]
    (hf : Function.Injective f) (hfg : Function.Exact f g) {s s' : W →ₗ[K] V}
    (hs : g ∘ₗ s = LinearMap.id) (hs' : g ∘ₗ s' = LinearMap.id) {n : ℕ}
    (hn : finrank K (U × W) = n) (x : Orientation K (U × W) (Fin n)) :
    map (Fin n) (splitEquiv hf hfg s hs) x = map (Fin n) (splitEquiv hf hfg s' hs') x := by
  have h := (map_eq_iff_det_pos x
    ((splitEquiv hf hfg s hs).trans (splitEquiv hf hfg s' hs').symm)
    (by rw [Fintype.card_fin, hn])).2 (det_splitEquiv_trans_symm_pos hf hfg hs hs')
  rw [map_trans, ← map_symm] at h
  exact (Equiv.symm_apply_eq _).1 h

/-! ### The orientation of the middle term -/

variable [FiniteDimensional K U] [FiniteDimensional K W]

/-- The orientation of `V` induced by orientations of `U` and `W` through a short exact sequence
`0 → U → V → W → 0`, with the subspace `U` first: a basis of `V` is positive when it consists of
the image of a positive basis of `U` followed by lifts of a positive basis of `W`
(`Orientation.shortExact_basis_orientation`). -/
def shortExact (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c))
    (ha : finrank K U = a) (hc : finrank K W = c) : Orientation K V (Fin (a + c)) :=
  map (Fin (a + c)) (splitEquiv hf hfg _ (exists_section hg).choose_spec) (prod o p ha hc)

variable (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
  (ha : finrank K U = a) (hc : finrank K W = c)

private theorem shortExact_eq_map_splitEquiv (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) (s : W →ₗ[K] V) (hs : g ∘ₗ s = LinearMap.id) :
    shortExact hf hfg hg o p ha hc = map (Fin (a + c)) (splitEquiv hf hfg s hs) (prod o p ha hc) :=
  map_splitEquiv_eq hf hfg _ hs (by rw [Module.finrank_prod, ha, hc]) _

/-- The induced orientation is the product orientation transported along the splitting
`(u, w) ↦ f u + s w` given by any section `s` of `g`. -/
theorem shortExact_eq_map_prod (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c))
    (s : W →ₗ[K] V) (hs : g ∘ₗ s = LinearMap.id) :
    shortExact hf hfg hg o p ha hc =
      map (Fin (a + c)) ((hfg.splitSurjectiveEquiv hf ⟨s, hs⟩).1.symm) (prod o p ha hc) :=
  shortExact_eq_map_splitEquiv hf hfg hg ha hc o p s hs

/-- A basis of `V` consisting of the image of a basis `b` of `U` followed by lifts of a basis `e`
of `W` has the orientation induced by the orientations of `b` and `e`. -/
theorem shortExact_basis_orientation (b : Basis (Fin a) K U) (e : Basis (Fin c) K W)
    (B : Basis (Fin (a + c)) K V) (hB₁ : ∀ i, B (Fin.castAdd c i) = f (b i))
    (hB₂ : ∀ j, g (B (Fin.natAdd a j)) = e j) :
    shortExact hf hfg hg b.orientation e.orientation ha hc = B.orientation := by
  set s : W →ₗ[K] V := e.constr K fun j ↦ B (Fin.natAdd a j)
  have hs : g ∘ₗ s = LinearMap.id := e.ext fun j ↦ by simp [s, hB₂]
  rw [shortExact_eq_map_splitEquiv hf hfg hg ha hc _ _ s hs, prod_basis_orientation,
    ← Basis.orientation_map]
  congr 1
  refine Basis.eq_of_apply_eq fun k ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · rw [hB₁]
    exact (splitEquiv_apply hf hfg s hs _).trans (by simp [Basis.prod_apply])
  · exact (splitEquiv_apply hf hfg s hs _).trans (by simp [Basis.prod_apply, s])

/-- Reversing the orientation of the subspace reverses the induced orientation. -/
@[simp]
theorem shortExact_neg_left (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg (-o) p ha hc = -shortExact hf hfg hg o p ha hc := by
  simp only [shortExact, prod_neg_left, Orientation.map_neg]

/-- Reversing the orientation of the quotient reverses the induced orientation. -/
@[simp]
theorem shortExact_neg_right (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg o (-p) ha hc = -shortExact hf hfg hg o p ha hc := by
  simp only [shortExact, prod_neg_right, Orientation.map_neg]

/-- Scaling the orientation of the subspace by a unit scales the induced orientation. -/
@[simp]
theorem shortExact_units_smul_left (u : Kˣ) (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg (u • o) p ha hc = u • shortExact hf hfg hg o p ha hc := by
  rcases lt_or_gt_of_ne u.ne_zero with hu | hu
  · simp only [Module.Ray.units_smul_of_neg u hu, shortExact_neg_left]
  · simp only [Module.Ray.units_smul_of_pos u hu]

/-- Scaling the orientation of the quotient by a unit scales the induced orientation. -/
@[simp]
theorem shortExact_units_smul_right (u : Kˣ) (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg o (u • p) ha hc = u • shortExact hf hfg hg o p ha hc := by
  rcases lt_or_gt_of_ne u.ne_zero with hu | hu
  · simp only [Module.Ray.units_smul_of_neg u hu, shortExact_neg_right]
  · simp only [Module.Ray.units_smul_of_pos u hu]

/-- The induced orientation determines the orientation of the subspace. -/
theorem shortExact_inj_left {o o' : Orientation K U (Fin a)} (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg o p ha hc = shortExact hf hfg hg o' p ha hc ↔ o = o' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rcases o.eq_or_eq_neg o' (by rw [Fintype.card_fin, ha]) with ho | ho
  · exact ho
  · rw [ho, shortExact_neg_left] at h
    exact absurd h (Module.Ray.ne_neg_self _).symm

/-- The induced orientation determines the orientation of the quotient. -/
theorem shortExact_inj_right (o : Orientation K U (Fin a)) {p p' : Orientation K W (Fin c)} :
    shortExact hf hfg hg o p ha hc = shortExact hf hfg hg o p' ha hc ↔ p = p' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rcases p.eq_or_eq_neg p' (by rw [Fintype.card_fin, hc]) with hp | hp
  · exact hp
  · rw [hp, shortExact_neg_right] at h
    exact absurd h (Module.Ray.ne_neg_self _).symm

/-- The induced orientation is natural for isomorphisms of short exact sequences: if linear
equivalences `U ≃ U'`, `V ≃ V'` and `W ≃ W'` commute with the maps of two short exact sequences,
then the equivalence of the middle terms carries the induced orientation to the orientation induced
by the transported outer orientations. -/
theorem map_shortExact {U' V' W' : Type*} [AddCommGroup U'] [Module K U'] [AddCommGroup V']
    [Module K V'] [AddCommGroup W'] [Module K W'] [FiniteDimensional K U']
    [FiniteDimensional K W'] {f' : U' →ₗ[K] V'} {g' : V' →ₗ[K] W'}
    (hf' : Function.Injective f') (hfg' : Function.Exact f' g') (hg' : Function.Surjective g')
    (eU : U ≃ₗ[K] U') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (h₁ : f' ∘ₗ eU = eV ∘ₗ f) (h₂ : g' ∘ₗ eV = eW ∘ₗ g)
    (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c)) :
    map (Fin (a + c)) eV (shortExact hf hfg hg o p ha hc) =
      shortExact hf' hfg' hg' (map (Fin a) eU o) (map (Fin c) eW p)
        (eU.finrank_eq.symm.trans ha) (eW.finrank_eq.symm.trans hc) := by
  obtain ⟨s, hs⟩ := exists_section hg
  set s' : W' →ₗ[K] V' := eV.toLinearMap ∘ₗ s ∘ₗ eW.symm.toLinearMap
  have hs' : g' ∘ₗ s' = LinearMap.id := by
    ext w
    have h := LinearMap.congr_fun h₂ (s (eW.symm w))
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    have hgs : g (s (eW.symm w)) = eW.symm w := LinearMap.congr_fun hs _
    simp [s', h, hgs]
  have hsplit : (splitEquiv hf hfg s hs).trans eV =
      (eU.prodCongr eW).trans (splitEquiv hf' hfg' s' hs') := by
    ext1 x
    have h := LinearMap.congr_fun h₁ x.1
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    simp [splitEquiv_apply, s', h]
  rw [shortExact_eq_map_splitEquiv hf hfg hg ha hc o p s hs,
    shortExact_eq_map_splitEquiv hf' hfg' hg' (eU.finrank_eq.symm.trans ha)
      (eW.finrank_eq.symm.trans hc) _ _ s' hs', ← map_prod, ← map_trans, ← map_trans, hsplit]

/-! ### The orientation of the subspace -/

/-- The orientation of `U` induced by orientations of `V` and `W` through a short exact sequence
`0 → U → V → W → 0`: the unique orientation `o` of `U` for which the subspace-first orientation
`Orientation.shortExact` of `o` and `p` is the given orientation of `V`
(`Orientation.shortExactLeft_eq_iff`). -/
def shortExactLeft (ov : Orientation K V (Fin (a + c))) (p : Orientation K W (Fin c)) :
    Orientation K U (Fin a) := by
  classical
  exact if shortExact hf hfg hg (finBasisOfFinrankEq K U ha).orientation p ha hc = ov then
    (finBasisOfFinrankEq K U ha).orientation else -(finBasisOfFinrankEq K U ha).orientation

/-- The subspace orientation induces back the given orientation of `V`. -/
@[simp]
theorem shortExact_shortExactLeft (ov : Orientation K V (Fin (a + c)))
    (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg (shortExactLeft hf hfg hg ha hc ov p) p ha hc = ov := by
  have := Module.Finite.of_exact hfg hg
  have hV : Fintype.card (Fin (a + c)) = finrank K V := by
    rw [Fintype.card_fin, hfg.finrank_eq_add hf hg, ha, hc]
  unfold shortExactLeft
  split_ifs with h
  · exact h
  · rw [shortExact_neg_left, ((shortExact hf hfg hg _ p ha hc).eq_or_eq_neg ov hV).resolve_left h]
    exact neg_neg ov

/-- The subspace orientation is characterized by inducing the given orientation of `V`. -/
theorem shortExactLeft_eq_iff (ov : Orientation K V (Fin (a + c)))
    (p : Orientation K W (Fin c)) (o : Orientation K U (Fin a)) :
    shortExactLeft hf hfg hg ha hc ov p = o ↔ shortExact hf hfg hg o p ha hc = ov := by
  rw [← shortExact_inj_left hf hfg hg ha hc p, shortExact_shortExactLeft, eq_comm]

/-- The subspace orientation recovered from an induced orientation is the original one. -/
@[simp]
theorem shortExactLeft_shortExact (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c)) :
    shortExactLeft hf hfg hg ha hc (shortExact hf hfg hg o p ha hc) p = o :=
  (shortExactLeft_eq_iff hf hfg hg ha hc _ p o).2 rfl

/-- Reversing the orientation of `V` reverses the induced subspace orientation. -/
@[simp]
theorem shortExactLeft_neg_left (ov : Orientation K V (Fin (a + c)))
    (p : Orientation K W (Fin c)) :
    shortExactLeft hf hfg hg ha hc (-ov) p = -shortExactLeft hf hfg hg ha hc ov p := by
  rw [shortExactLeft_eq_iff, shortExact_neg_left, shortExact_shortExactLeft]

/-- Reversing the orientation of the quotient reverses the induced subspace orientation. -/
@[simp]
theorem shortExactLeft_neg_right (ov : Orientation K V (Fin (a + c)))
    (p : Orientation K W (Fin c)) :
    shortExactLeft hf hfg hg ha hc ov (-p) = -shortExactLeft hf hfg hg ha hc ov p := by
  rw [shortExactLeft_eq_iff, shortExact_neg_left, shortExact_neg_right, shortExact_shortExactLeft]
  exact neg_neg ov

end Orientation
