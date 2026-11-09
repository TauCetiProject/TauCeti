/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Prod
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.Ray

/-!
# Orientations of short exact sequences

Let `0 → U → V → W → 0` be a short exact sequence of finite-dimensional vector spaces over a
linearly ordered field, with maps `f : U → V` and `g : V → W`. Orientations of `U` and of `W`
orient `V`, **subspace first** (`Orientation.shortExact`): if `u₁, …, uₐ` is a positive basis of
`U` and `v₁, …, v_c` are lifts along `g` of a positive basis of `W`, then
`f u₁, …, f uₐ, v₁, …, v_c` is a positive basis of `V` (`Orientation.shortExact_basis_orientation`).
The orientation does not depend on the lifts: it is the transport of the product orientation along
the splitting `(u, w) ↦ f u + s w` for any linear section `s` of `g`
(`Orientation.shortExact_eq_map_prod`). Both facts reduce to the subspace-first bases
`Module.Basis.ofExactLift`, whose transition determinants do not depend on the lifts
(`Module.Basis.ofExactLift_det_ofExactLift`).

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

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem exists_section (hg : Function.Surjective g) :
    ∃ s : W →ₗ[K] V, g ∘ₗ s = LinearMap.id :=
  g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)

/-- The subspace-first basis `Module.Basis.ofExactLift` of `V` has an orientation independent of
the lifts: the transition determinant between two choices is `b.det b * e.det e = 1`. -/
private theorem orientation_reindex_ofExactLift (hf : Function.Injective f)
    (hfg : Function.Exact f g) (b : Basis (Fin a) K U) (e : Basis (Fin c) K W) {t t' : Fin c → V}
    (ht : ∀ j, g (t j) = e j) (ht' : ∀ j, g (t' j) = e j) :
    ((Basis.ofExactLift hf hfg b e t ht).reindex finSumFinEquiv).orientation =
      ((Basis.ofExactLift hf hfg b e t' ht').reindex finSumFinEquiv).orientation := by
  rw [Basis.orientation_reindex, Basis.orientation_reindex,
    (Basis.orientation_eq_iff_det_pos (Basis.ofExactLift hf hfg b e t ht) _).2]
  simp [Basis.ofExactLift_det_ofExactLift, Basis.det_self]

variable [FiniteDimensional K U] [FiniteDimensional K W]

/-- The splitting of a short exact sequence along any section carries the product orientation of
bases `b` of `U` and `e` of `W` to the orientation of the subspace-first basis of `V` made of
`f ∘ b` followed by any lifts `t` of `e`. -/
private theorem map_splitSurjectiveEquiv_prod_basis (hf : Function.Injective f)
    (hfg : Function.Exact f g) (l : { l : W →ₗ[K] V // g ∘ₗ l = LinearMap.id })
    (b : Basis (Fin a) K U) (e : Basis (Fin c) K W) (t : Fin c → V) (ht : ∀ j, g (t j) = e j)
    (ha : finrank K U = a) (hc : finrank K W = c) :
    map (Fin (a + c)) (hfg.splitSurjectiveEquiv hf l).1.symm
        (prod b.orientation e.orientation ha hc) =
      ((Basis.ofExactLift hf hfg b e t ht).reindex finSumFinEquiv).orientation := by
  obtain ⟨hφf, hφg⟩ := (hfg.splitSurjectiveEquiv hf l).2
  set φ := (hfg.splitSurjectiveEquiv hf l).1
  rw [prod_basis_orientation, ← Basis.orientation_map]
  set B := ((b.prod e).reindex finSumFinEquiv).map φ.symm
  have hB₁ (i : Fin a) : B (Fin.castAdd c i) = f (b i) := by
    simpa [B, Basis.prod_apply] using (LinearMap.congr_fun hφf (b i)).symm
  have hB₂ (j : Fin c) : g (B (Fin.natAdd a j)) = e j := by
    simpa [B, Basis.prod_apply] using LinearMap.congr_fun hφg (φ.symm (0, e j))
  rw [Basis.eq_reindex_ofExactLift hf hfg b e B hB₁ hB₂]
  exact orientation_reindex_ofExactLift hf hfg b e _ _

/-- The splittings along any two sections carry an orientation of `U × W` to the same orientation
of `V`. -/
private theorem map_splitSurjectiveEquiv_eq (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (l l' : { l : W →ₗ[K] V // g ∘ₗ l = LinearMap.id }) (ha : finrank K U = a)
    (hc : finrank K W = c) (x : Orientation K (U × W) (Fin (a + c))) :
    map (Fin (a + c)) (hfg.splitSurjectiveEquiv hf l).1.symm x =
      map (Fin (a + c)) (hfg.splitSurjectiveEquiv hf l').1.symm x := by
  set b := finBasisOfFinrankEq K U ha
  set e := finBasisOfFinrankEq K W hc
  choose t ht using fun j ↦ hg (e j)
  rcases x.eq_or_eq_neg (prod b.orientation e.orientation ha hc)
    (by rw [Fintype.card_fin, finrank_prod, ha, hc]) with rfl | rfl <;>
  simp only [Orientation.map_neg, map_splitSurjectiveEquiv_prod_basis hf hfg _ b e t ht]

/-! ### The orientation of the middle term -/

/-- The orientation of `V` induced by orientations of `U` and `W` through a short exact sequence
`0 → U → V → W → 0`, with the subspace `U` first: a basis of `V` is positive when it consists of
the image of a positive basis of `U` followed by lifts of a positive basis of `W`
(`Orientation.shortExact_basis_orientation`). -/
def shortExact (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c))
    (ha : finrank K U = a) (hc : finrank K W = c) : Orientation K V (Fin (a + c)) :=
  map (Fin (a + c)) (hfg.splitSurjectiveEquiv hf ⟨_, (exists_section hg).choose_spec⟩).1.symm
    (prod o p ha hc)

variable (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
  (ha : finrank K U = a) (hc : finrank K W = c)

/-- The induced orientation is the product orientation transported along the splitting
`(u, w) ↦ f u + s w` given by any section `s` of `g`. -/
theorem shortExact_eq_map_prod (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c))
    (s : W →ₗ[K] V) (hs : g ∘ₗ s = LinearMap.id) :
    shortExact hf hfg hg o p ha hc =
      map (Fin (a + c)) ((hfg.splitSurjectiveEquiv hf ⟨s, hs⟩).1.symm) (prod o p ha hc) :=
  map_splitSurjectiveEquiv_eq hf hfg hg _ _ ha hc _

/-- A basis of `V` consisting of the image of a basis `b` of `U` followed by lifts of a basis `e`
of `W` has the orientation induced by the orientations of `b` and `e`. -/
theorem shortExact_basis_orientation (b : Basis (Fin a) K U) (e : Basis (Fin c) K W)
    (B : Basis (Fin (a + c)) K V) (hB₁ : ∀ i, B (Fin.castAdd c i) = f (b i))
    (hB₂ : ∀ j, g (B (Fin.natAdd a j)) = e j) :
    shortExact hf hfg hg b.orientation e.orientation ha hc = B.orientation := by
  rw [shortExact, map_splitSurjectiveEquiv_prod_basis hf hfg _ b e _ hB₂,
    ← Basis.eq_reindex_ofExactLift hf hfg b e B hB₁ hB₂]

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
    shortExact hf hfg hg (u • o) p ha hc = u • shortExact hf hfg hg o p ha hc :=
  Module.Ray.units_smul_of_map_neg (F := (shortExact hf hfg hg · p ha hc))
    (shortExact_neg_left hf hfg hg ha hc · p) u o

/-- Scaling the orientation of the quotient by a unit scales the induced orientation. -/
@[simp]
theorem shortExact_units_smul_right (u : Kˣ) (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg o (u • p) ha hc = u • shortExact hf hfg hg o p ha hc :=
  Module.Ray.units_smul_of_map_neg (F := (shortExact hf hfg hg o · ha hc))
    (shortExact_neg_right hf hfg hg ha hc o ·) u p

/-- The induced orientation determines the orientation of the subspace. -/
@[simp]
theorem shortExact_inj_left {o o' : Orientation K U (Fin a)} (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg o p ha hc = shortExact hf hfg hg o' p ha hc ↔ o = o' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rcases o.eq_or_eq_neg o' (by rw [Fintype.card_fin, ha]) with ho | ho
  · exact ho
  · rw [ho, shortExact_neg_left] at h
    exact absurd h (Module.Ray.ne_neg_self _).symm

/-- The induced orientation determines the orientation of the quotient. -/
@[simp]
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
  set b := finBasisOfFinrankEq K U ha
  set e := finBasisOfFinrankEq K W hc
  choose t ht using fun j ↦ hg (e j)
  set B := (Basis.ofExactLift hf hfg b e t ht).reindex finSumFinEquiv
  have hB₁ (i : Fin a) : B (Fin.castAdd c i) = f (b i) := by simp [B]
  have hB₂ (j : Fin c) : g (B (Fin.natAdd a j)) = e j := by simp [B, ht]
  -- The image of `B` under `eV` is again subspace-first, for the transported bases.
  have hB₁' (i : Fin a) : (B.map eV) (Fin.castAdd c i) = f' ((b.map eU) i) := by
    simpa [hB₁] using (LinearMap.congr_fun h₁ (b i)).symm
  have hB₂' (j : Fin c) : g' ((B.map eV) (Fin.natAdd a j)) = (e.map eW) j := by
    simpa [hB₂] using LinearMap.congr_fun h₂ (B (Fin.natAdd a j))
  have key : map (Fin (a + c)) eV (shortExact hf hfg hg b.orientation e.orientation ha hc) =
      shortExact hf' hfg' hg' (map (Fin a) eU b.orientation) (map (Fin c) eW e.orientation)
        (eU.finrank_eq.symm.trans ha) (eW.finrank_eq.symm.trans hc) := by
    rw [shortExact_basis_orientation hf hfg hg ha hc b e B hB₁ hB₂, ← Basis.orientation_map,
      ← Basis.orientation_map, ← Basis.orientation_map,
      shortExact_basis_orientation hf' hfg' hg' _ _ _ _ _ hB₁' hB₂']
  rcases o.eq_or_eq_neg b.orientation (by rw [Fintype.card_fin, ha]) with rfl | rfl <;>
  rcases p.eq_or_eq_neg e.orientation (by rw [Fintype.card_fin, hc]) with rfl | rfl <;>
  simp only [shortExact_neg_left, shortExact_neg_right, Orientation.map_neg, key]

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

/-- Scaling the orientation of `V` by a unit scales the induced subspace orientation. -/
@[simp]
theorem shortExactLeft_units_smul_left (u : Kˣ) (ov : Orientation K V (Fin (a + c)))
    (p : Orientation K W (Fin c)) :
    shortExactLeft hf hfg hg ha hc (u • ov) p = u • shortExactLeft hf hfg hg ha hc ov p :=
  Module.Ray.units_smul_of_map_neg (F := (shortExactLeft hf hfg hg ha hc · p))
    (shortExactLeft_neg_left hf hfg hg ha hc · p) u ov

/-- Scaling the orientation of the quotient by a unit scales the induced subspace orientation. -/
@[simp]
theorem shortExactLeft_units_smul_right (u : Kˣ) (ov : Orientation K V (Fin (a + c)))
    (p : Orientation K W (Fin c)) :
    shortExactLeft hf hfg hg ha hc ov (u • p) = u • shortExactLeft hf hfg hg ha hc ov p :=
  Module.Ray.units_smul_of_map_neg (F := (shortExactLeft hf hfg hg ha hc ov ·))
    (shortExactLeft_neg_right hf hfg hg ha hc ov ·) u p

end Orientation
