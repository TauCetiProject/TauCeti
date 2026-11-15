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
public import TauCeti.Algebra.Module.LinearMap.Defs
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.LinearAlgebra.Orientation.Exact
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
(`Module.Basis.ofExactLift_det_ofExactLift`). Over a field this is the orientation
`Orientation.ofExact` of short exact sequences of finite free modules
(`Orientation.shortExact_eq_ofExact`).

Conversely, orientations of `V` and `W` determine a unique orientation of `U`
(`Orientation.shortExactLeft`), characterized by `Orientation.shortExactLeft_eq_iff`. This is how
the orientation of a submanifold is induced from an orientation of the ambient space and of its
normal space, as in the orientation of transverse intersections and fibre products
(`TauCeti.LinearAlgebra.Orientation.FiberProduct`) and of spaces of gradient trajectories in Morse
homology. The construction is natural for isomorphisms of short exact sequences
(`Orientation.map_shortExact`), and reversing either outer orientation reverses the middle one.

This is the orientation counterpart of the determinant-line isomorphism
`TauCeti.detLineShortExactEquiv`, which uses the same subspace-first order.

Subspace-first orientations compose along towers. If `U' ⊆ U ⊆ V` with quotients `U / U' ≅ B`
and `V / U ≅ A`, and the map `U → B` extends to `V`, then orienting `U` from `U'` and `B` and
then `V` from `U` and `A` is the same as orienting `V` from `U'` and the product `[B][A]`
(`Orientation.shortExact_shortExact`). Consequently, when a linear equivalence carries such a
tower onto one that cuts out the same subspace in the opposite order, the induced orientations
differ by `(-1) ^ (dim A · dim B)` (`Orientation.map_shortExact_shortExact`). Adjoining a further
factor `Z` to a short exact sequence after the subspace costs the sign `(-1) ^ (dim Z · dim W)`
of moving `Z` past `W`, while adjoining it before costs nothing
(`Orientation.shortExact_prodMap_id`, `Orientation.shortExact_id_prodMap`). These are the
bookkeeping identities behind the associativity of fibre product orientations
(`Orientation.map_fiberProduct_assoc`).

## Main definitions

* `Orientation.shortExact`: the orientation of `V` induced by orientations of `U` and `W`.
* `Orientation.shortExactLeft`: the orientation of `U` induced by orientations of `V` and `W`.

## Main results

* `Orientation.shortExact_eq_map_prod`: the induced orientation is the product orientation
  transported along the splitting given by any section.
* `Orientation.shortExact_basis_orientation`: a basis of `V` made of the image of a basis of `U`
  followed by lifts of a basis of `W` has the induced orientation.
* `Orientation.shortExact_eq_ofExact`: the induced orientation is `Orientation.ofExact`.
* `Orientation.map_shortExact`: naturality for isomorphisms of short exact sequences.
* `Orientation.shortExact_inj_left`, `Orientation.shortExact_inj_right`: the induced orientation
  determines each outer orientation given the other.
* `Orientation.shortExactLeft_eq_iff`: the characterization of `Orientation.shortExactLeft`.
* `Orientation.shortExact_inl_snd`: the product orientation is that of the split sequence.
* `Orientation.shortExact_shortExact`: subspace-first orientations compose along towers.
* `Orientation.map_shortExact_shortExact`: exchanging the two stages of a tower costs
  `(-1) ^ (dim A · dim B)`.
* `Orientation.shortExact_prodMap_id`, `Orientation.shortExact_id_prodMap`: adjoining a further
  factor after or before the subspace.

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

/-- Over a field, the induced orientation is the orientation `Orientation.ofExact` of a short
exact sequence of finite free modules. -/
theorem shortExact_eq_ofExact (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c)) :
    shortExact hf hfg hg o p ha hc = ofExact hf hfg hg o p ha hc := by
  set eU := finBasisOfFinrankEq K U ha
  set eW := finBasisOfFinrankEq K W hc
  -- Both orientations are fixed by the same subspace-first basis.
  have key : shortExact hf hfg hg eU.orientation eW.orientation ha hc =
      ofExact hf hfg hg eU.orientation eW.orientation ha hc := by
    choose t ht using fun j ↦ hg (eW j)
    set B := (Basis.ofExactLift hf hfg eU eW t ht).reindex finSumFinEquiv
    rw [shortExact_basis_orientation hf hfg hg ha hc eU eW B (by simp [B]) (by simp [B, ht]),
      ofExact_orientation hf hfg hg eU eW B (by simp [B]) (by simp [B, ht]) ha hc]
  rcases eU.orientation_eq_or_eq_neg o with rfl | rfl <;>
  rcases eW.orientation_eq_or_eq_neg p with rfl | rfl <;>
  simp only [shortExact_neg_left, shortExact_neg_right, ofExact_neg_left, ofExact_neg_right, key]

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

namespace Orientation

/-! ### Recasting the index types -/

section Reindex

variable {K U V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K U] [FiniteDimensional K W] {f : U →ₗ[K] V} {g : V →ₗ[K] W} {a c : ℕ}
  (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)

/-- Recasting the index type of the subspace orientation recasts that of the induced one. -/
theorem shortExact_reindex_finCongr_left {a' : ℕ} (e : a = a') (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) (ha : finrank K U = a') (hc : finrank K W = c) :
    shortExact hf hfg hg (reindex K U (finCongr e) o) p ha hc =
      reindex K V (finCongr (congrArg (· + c) e))
        (shortExact hf hfg hg o p (ha.trans e.symm) hc) := by
  subst e
  simp [finCongr_refl, reindex_refl]

/-- Recasting the index type of the quotient orientation recasts that of the induced one. -/
theorem shortExact_reindex_finCongr_right {c' : ℕ} (e : c = c') (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) (ha : finrank K U = a) (hc : finrank K W = c') :
    shortExact hf hfg hg o (reindex K W (finCongr e) p) ha hc =
      reindex K V (finCongr (congrArg (a + ·) e))
        (shortExact hf hfg hg o p ha (hc.trans e.symm)) := by
  subst e
  simp [finCongr_refl, reindex_refl]

end Reindex

/-! ### Towers of short exact sequences -/

section Tower

variable {K U' U V B A : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup U'] [Module K U'] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup B] [Module K B] [AddCommGroup A] [Module K A]
  [FiniteDimensional K U'] [FiniteDimensional K U] [FiniteDimensional K B]
  [FiniteDimensional K A]
  {f' : U' →ₗ[K] U} {g' : U →ₗ[K] B} {f : U →ₗ[K] V} {g : V →ₗ[K] A} {h : V →ₗ[K] B}
  {a b c : ℕ}

/-- **Towers of short exact sequences.** Let `0 → U' → U → B → 0` and `0 → U → V → A → 0` be
short exact, and let `h : V → B` extend `g' : U → B` along `f`, so that
`0 → U' → V → B × A → 0` is short exact with quotient map `v ↦ (h v, g v)`. Orienting `U` from
`U'` and `B`, and then `V` from `U` and `A`, gives the orientation of `V` induced by `U'` and the
product orientation of `B × A`: in a subspace-first basis, a basis of `U'` is followed by lifts of
a basis of `B` and then by lifts of a basis of `A`. -/
theorem shortExact_shortExact (hf' : Function.Injective f') (hfg' : Function.Exact f' g')
    (hg' : Function.Surjective g') (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hhf : h ∘ₗ f = g')
    (o : Orientation K U' (Fin a)) (p : Orientation K B (Fin b)) (q : Orientation K A (Fin c))
    (ha : finrank K U' = a) (hb : finrank K B = b) (hc : finrank K A = c)
    (hab : finrank K U = a + b) :
    shortExact hf hfg hg (shortExact hf' hfg' hg' o p ha hb) q hab hc =
      reindex K V (finCongr (add_assoc a b c).symm)
        (shortExact (f := f ∘ₗ f') (g := h.prod g) (LinearMap.injective_comp hf hf')
          (hfg'.comp_prod hfg hhf)
          (LinearMap.surjective_prod_of_comp_eq_zero hfg.linearMap_comp_eq_zero (hhf ▸ hg') hg)
          o (prod p q hb hc) ha (by rw [finrank_prod, hb, hc])) := by
  set eU := finBasisOfFinrankEq K U' ha
  set eB := finBasisOfFinrankEq K B hb
  set eA := finBasisOfFinrankEq K A hc
  suffices key : shortExact hf hfg hg (shortExact hf' hfg' hg' eU.orientation eB.orientation ha hb)
      eA.orientation hab hc = reindex K V (finCongr (add_assoc a b c).symm)
        (shortExact (f := f ∘ₗ f') (g := h.prod g) (LinearMap.injective_comp hf hf')
          (hfg'.comp_prod hfg hhf)
          (LinearMap.surjective_prod_of_comp_eq_zero hfg.linearMap_comp_eq_zero (hhf ▸ hg') hg)
          eU.orientation (prod eB.orientation eA.orientation hb hc) ha
          (by rw [finrank_prod, hb, hc])) by
    rcases eU.orientation_eq_or_eq_neg o with rfl | rfl <;>
    rcases eB.orientation_eq_or_eq_neg p with rfl | rfl <;>
    rcases eA.orientation_eq_or_eq_neg q with rfl | rfl <;>
    simp only [shortExact_neg_left, shortExact_neg_right, prod_neg_left, prod_neg_right,
      Orientation.reindex_neg, key]
  -- Lifts of the basis of `A` are chosen in the kernel of `h`, so that the subspace-first basis
  -- of the tower is also subspace-first for `0 → U' → V → B × A → 0`.
  choose tB htB using fun j ↦ hg' (eB j)
  choose tA htA using fun i ↦
    LinearMap.surjective_prod_of_comp_eq_zero hfg.linearMap_comp_eq_zero (hhf ▸ hg') hg (0, eA i)
  have htA₂ (i : Fin c) : g (tA i) = eA i := congrArg Prod.snd (htA i)
  set BU := (Basis.ofExactLift hf' hfg' eU eB tB htB).reindex finSumFinEquiv
  have hU : shortExact hf' hfg' hg' eU.orientation eB.orientation ha hb = BU.orientation :=
    shortExact_basis_orientation hf' hfg' hg' ha hb eU eB BU (by simp [BU]) (by simp [BU, htB])
  set BV := (Basis.ofExactLift hf hfg BU eA tA htA₂).reindex finSumFinEquiv
  have hV : shortExact hf hfg hg BU.orientation eA.orientation hab hc = BV.orientation :=
    shortExact_basis_orientation hf hfg hg hab hc BU eA BV (by simp [BV]) (by simp [BV, htA₂])
  rw [hU, hV, prod_basis_orientation,
    shortExact_basis_orientation _ _ _ ha _ eU _ (BV.reindex (finCongr (add_assoc a b c)))]
  · rw [Basis.orientation_reindex BV (finCongr (add_assoc a b c)),
      ← finCongr_symm (add_assoc a b c), ← reindex_symm, Equiv.symm_apply_apply]
  · intro i
    have : Fin.cast (add_assoc a b c).symm (Fin.castAdd (b + c) i) =
        Fin.castAdd c (Fin.castAdd b i) := Fin.ext rfl
    simp [BV, BU, this]
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_)
    · have : Fin.cast (add_assoc a b c).symm (Fin.natAdd a (Fin.castAdd c j)) =
          Fin.castAdd c (Fin.natAdd a j) := Fin.ext rfl
      simp only [BV, BU, Basis.reindex_apply, finCongr_symm, finCongr_apply, this,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Basis.ofExactLift_inl, Basis.ofExactLift_inr, Basis.prod_apply, Sum.elim_inl,
        Function.comp_apply, LinearMap.inl_apply, LinearMap.prod_apply, Function.prod]
      rw [← LinearMap.comp_apply h, hhf, htB, hfg.apply_apply_eq_zero]
    · have : Fin.cast (add_assoc a b c).symm (Fin.natAdd a (Fin.natAdd b j)) =
          Fin.natAdd (a + b) j := Fin.ext (Nat.add_assoc a b j).symm
      simp [BV, BU, this, Basis.prod_apply, htA]

end Tower

/-! ### Exchanging the two stages of a tower -/

section Exchange

variable {K U₁' U₁ V₁ U₂' U₂ V₂ A B : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup U₁'] [Module K U₁'] [AddCommGroup U₁] [Module K U₁] [AddCommGroup V₁]
  [Module K V₁] [AddCommGroup U₂'] [Module K U₂'] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup V₂] [Module K V₂] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [FiniteDimensional K U₁'] [FiniteDimensional K U₁] [FiniteDimensional K U₂']
  [FiniteDimensional K U₂] [FiniteDimensional K A] [FiniteDimensional K B]
  {f₁' : U₁' →ₗ[K] U₁} {g₁' : U₁ →ₗ[K] B} {f₁ : U₁ →ₗ[K] V₁} {g₁ : V₁ →ₗ[K] A} {h₁ : V₁ →ₗ[K] B}
  {f₂' : U₂' →ₗ[K] U₂} {g₂' : U₂ →ₗ[K] A} {f₂ : U₂ →ₗ[K] V₂} {g₂ : V₂ →ₗ[K] B} {h₂ : V₂ →ₗ[K] A}
  {r a b : ℕ}

/-- **Exchanging the two stages of a tower.** Suppose a subspace is cut out of `V₁` in two stages,
first by `g₁ : V₁ → A` and then by `g₁' : U₁ → B` (with `h₁` extending `g₁'`), and that a linear
equivalence `V₁ ≃ V₂` carries it onto a subspace of `V₂` cut out in the opposite order, first by a
map to `B` and then by a map to `A`, compatibly with both quotient maps. Then the equivalence
carries the orientation induced by the first tower to `(-1) ^ (dim A · dim B)` times the one
induced by the second tower: the two quotients are exchanged. -/
theorem map_shortExact_shortExact (hf₁' : Function.Injective f₁')
    (hfg₁' : Function.Exact f₁' g₁') (hg₁' : Function.Surjective g₁')
    (hf₁ : Function.Injective f₁) (hfg₁ : Function.Exact f₁ g₁) (hg₁ : Function.Surjective g₁)
    (hh₁ : h₁ ∘ₗ f₁ = g₁') (hf₂' : Function.Injective f₂') (hfg₂' : Function.Exact f₂' g₂')
    (hg₂' : Function.Surjective g₂') (hf₂ : Function.Injective f₂)
    (hfg₂ : Function.Exact f₂ g₂) (hg₂ : Function.Surjective g₂) (hh₂ : h₂ ∘ₗ f₂ = g₂')
    (e : U₁' ≃ₗ[K] U₂') (eV : V₁ ≃ₗ[K] V₂) (hι : ∀ x, f₂ (f₂' (e x)) = eV (f₁ (f₁' x)))
    (hA : ∀ v, h₂ (eV v) = g₁ v) (hB : ∀ v, g₂ (eV v) = h₁ v)
    (o : Orientation K U₁' (Fin r)) (pA : Orientation K A (Fin a))
    (pB : Orientation K B (Fin b)) (hr : finrank K U₁' = r) (ha : finrank K A = a)
    (hb : finrank K B = b) (hrb : finrank K U₁ = r + b) (hra : finrank K U₂ = r + a) :
    map (Fin (r + b + a)) eV
        (shortExact hf₁ hfg₁ hg₁ (shortExact hf₁' hfg₁' hg₁' o pB hr hb) pA hrb ha) =
      (-1 : Kˣ) ^ (a * b) • reindex K V₂ (finCongr (add_right_comm r a b))
        (shortExact hf₂ hfg₂ hg₂ (shortExact hf₂' hfg₂' hg₂' (map (Fin r) e o) pA
          (e.finrank_eq.symm.trans hr) ha) pB hra hb) := by
  -- Collapse both towers to single short exact sequences, and transport the first one along `eV`,
  -- which carries its quotient `B × A` to the quotient `A × B` of the second.
  rw [shortExact_shortExact hf₁' hfg₁' hg₁' hf₁ hfg₁ hg₁ hh₁,
    shortExact_shortExact hf₂' hfg₂' hg₂' hf₂ hfg₂ hg₂ hh₂, map_reindex,
    map_shortExact (f := f₁ ∘ₗ f₁') (g := h₁.prod g₁) (LinearMap.injective_comp hf₁ hf₁')
      (hfg₁'.comp_prod hfg₁ hh₁)
      (LinearMap.surjective_prod_of_comp_eq_zero hfg₁.linearMap_comp_eq_zero (hh₁ ▸ hg₁') hg₁) hr
      (by rw [finrank_prod, hb, ha]) (f' := f₂ ∘ₗ f₂') (g' := h₂.prod g₂)
      (LinearMap.injective_comp hf₂ hf₂')
      (hfg₂'.comp_prod hfg₂ hh₂)
      (LinearMap.surjective_prod_of_comp_eq_zero hfg₂.linearMap_comp_eq_zero (hh₂ ▸ hg₂') hg₂)
      e eV (LinearEquiv.prodComm K B A) (LinearMap.ext hι)
      (LinearMap.ext fun v ↦ Prod.ext (hA v) (hB v)),
    map_prodComm_prod, shortExact_units_smul_right,
    shortExact_reindex_finCongr_right, mul_comm b a]
  -- Normalize the reindexings.
  simp only [reindex_units_smul, reindex_finCongr_reindex_finCongr]

end Exchange

/-! ### Products with a further factor -/

section Factor

variable {K U V W Z : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K U] [FiniteDimensional K W]
  [FiniteDimensional K Z] {a c z : ℕ}

/-- The product orientation of `U × W` is the subspace-first orientation of the split sequence
`0 → U → U × W → W → 0`. -/
theorem shortExact_inl_snd (o : Orientation K U (Fin a)) (p : Orientation K W (Fin c))
    (ha : finrank K U = a) (hc : finrank K W = c) :
    shortExact (LinearMap.inl_injective (R := K) (M := U) (M₂ := W)) Function.Exact.inl_snd
      LinearMap.snd_surjective o p ha hc = prod o p ha hc := by
  rw [shortExact_eq_ofExact, ofExact_inl_snd]

variable [FiniteDimensional K V] {f : U →ₗ[K] V} {g : V →ₗ[K] W} (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

/-- **A further factor after the subspace.** For a short exact sequence `0 → U → V → W → 0` and a
space `Z`, orient `V × Z` through `0 → U × Z → V × Z → W → 0` from `[U][Z]` and `[W]`. This is the
product of the induced orientation of `V` with `[Z]`, up to the sign `(-1) ^ (dim Z · dim W)` of
moving `Z` past `W`. -/
theorem shortExact_prodMap_id (o : Orientation K U (Fin a)) (oz : Orientation K Z (Fin z))
    (p : Orientation K W (Fin c)) (ha : finrank K U = a) (hz : finrank K Z = z)
    (hc : finrank K W = c) :
    shortExact (f := f.prodMap (LinearMap.id : Z →ₗ[K] Z)) (g := g ∘ₗ LinearMap.fst K V Z)
        (LinearMap.injective_prodMap hf Function.injective_id) hfg.prodMap_id_comp_fst
        (LinearMap.surjective_comp hg LinearMap.fst_surjective) (prod o oz ha hz) p
        (by rw [finrank_prod, ha, hz]) hc =
      (-1 : Kˣ) ^ (z * c) • reindex K (V × Z) (finCongr (add_right_comm a c z))
        (prod (shortExact hf hfg hg o p ha hc) oz
          (by rw [hfg.finrank_eq_add hf hg, ha, hc]) hz) := by
  -- Both sides are towers over `V × Z`, after writing the product orientations of `U × Z` and of
  -- `V × Z` as subspace-first orientations of `U → U × Z → Z` and `V → V × Z → Z`. The two
  -- towers differ by the exchange of the quotient factors `Z` and `W`, which costs
  -- `(-1) ^ (c * z)` by `map_shortExact_shortExact`.
  have E := map_shortExact_shortExact LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective (LinearMap.injective_prodMap hf Function.injective_id)
    hfg.prodMap_id_comp_fst (LinearMap.surjective_comp hg LinearMap.fst_surjective)
    (h₁ := LinearMap.snd K V Z) (by ext <;> simp) hf hfg hg LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective (h₂ := g ∘ₗ LinearMap.fst K V Z)
    (by ext; simp) (LinearEquiv.refl K U) (LinearEquiv.refl K (V × Z)) (fun _ ↦ by simp)
    (fun _ ↦ rfl) (fun _ ↦ rfl) o p oz ha hc hz (by rw [finrank_prod, ha, hz])
    (by rw [hfg.finrank_eq_add hf hg, ha, hc])
  simp only [Orientation.map_refl, Equiv.refl_apply, shortExact_inl_snd] at E
  rw [E, mul_comm]

/-- **A further factor before the subspace.** For a short exact sequence `0 → U → V → W → 0` and a
space `Z`, orient `Z × V` through `0 → Z × U → Z × V → W → 0` from `[Z][U]` and `[W]`. This is the
product of `[Z]` with the induced orientation of `V`, with no sign. -/
theorem shortExact_id_prodMap (oz : Orientation K Z (Fin z)) (o : Orientation K U (Fin a))
    (p : Orientation K W (Fin c)) (hz : finrank K Z = z) (ha : finrank K U = a)
    (hc : finrank K W = c) :
    shortExact (f := (LinearMap.id : Z →ₗ[K] Z).prodMap f) (g := g ∘ₗ LinearMap.snd K Z V)
        (LinearMap.injective_prodMap Function.injective_id hf) hfg.id_prodMap_comp_snd
        (LinearMap.surjective_comp hg LinearMap.snd_surjective) (prod oz o hz ha) p
        (by rw [finrank_prod, hz, ha]) hc =
      reindex K (Z × V) (finCongr (add_assoc z a c).symm)
        (prod oz (shortExact hf hfg hg o p ha hc) hz
          (by rw [hfg.finrank_eq_add hf hg, ha, hc])) := by
  set eZ := finBasisOfFinrankEq K Z hz
  set eU := finBasisOfFinrankEq K U ha
  set eW := finBasisOfFinrankEq K W hc
  suffices key : shortExact (f := (LinearMap.id : Z →ₗ[K] Z).prodMap f)
      (g := g ∘ₗ LinearMap.snd K Z V) (LinearMap.injective_prodMap Function.injective_id hf)
      hfg.id_prodMap_comp_snd (LinearMap.surjective_comp hg LinearMap.snd_surjective)
      (prod eZ.orientation eU.orientation hz ha) eW.orientation
        (by rw [finrank_prod, hz, ha]) hc =
      reindex K (Z × V) (finCongr (add_assoc z a c).symm)
        (prod eZ.orientation (shortExact hf hfg hg eU.orientation eW.orientation ha hc) hz
          (by rw [hfg.finrank_eq_add hf hg, ha, hc])) by
    rcases eZ.orientation_eq_or_eq_neg oz with rfl | rfl <;>
    rcases eU.orientation_eq_or_eq_neg o with rfl | rfl <;>
    rcases eW.orientation_eq_or_eq_neg p with rfl | rfl <;>
    simp only [shortExact_neg_left, shortExact_neg_right, prod_neg_left, prod_neg_right,
      Orientation.reindex_neg, key]
  -- Both sides are oriented by the basis `(z, 0), (0, f u), (0, t)` for bases `z` of `Z`, `u` of
  -- `U` and lifts `t` of a basis of `W`.
  choose t ht using fun j ↦ hg (eW j)
  set BV := (Basis.ofExactLift hf hfg eU eW t ht).reindex finSumFinEquiv
  have hV : shortExact hf hfg hg eU.orientation eW.orientation ha hc = BV.orientation :=
    shortExact_basis_orientation hf hfg hg ha hc eU eW BV (by simp [BV]) (by simp [BV, ht])
  set B := (eZ.prod BV).reindex finSumFinEquiv
  rw [hV, prod_basis_orientation, prod_basis_orientation,
    shortExact_basis_orientation _ _ _ _ hc _ eW (B.reindex (finCongr (add_assoc z a c).symm)),
    Basis.orientation_reindex]
  · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)
    · have : Fin.cast (add_assoc z a c) (Fin.castAdd c (Fin.castAdd a i)) =
          Fin.castAdd (a + c) i := Fin.ext rfl
      simp [B, BV, this, Basis.prod_apply]
    · have : Fin.cast (add_assoc z a c) (Fin.castAdd c (Fin.natAdd z i)) =
          Fin.natAdd z (Fin.castAdd c i) := Fin.ext rfl
      simp [B, BV, this, Basis.prod_apply]
  · intro j
    have : Fin.cast (add_assoc z a c) (Fin.natAdd (z + a) j) =
        Fin.natAdd z (Fin.natAdd a j) := Fin.ext (Nat.add_assoc z a j)
    simp [B, BV, this, Basis.prod_apply, ht]

end Factor

end Orientation
