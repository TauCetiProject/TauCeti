/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Prod
public import Mathlib.Algebra.Exact.Basic
public import TauCeti.LinearAlgebra.Exact
import Mathlib.Algebra.Module.Projective
import TauCeti.LinearAlgebra.Basis.Exact
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

The subspace-first order is associative (`Orientation.shortExact_assoc`): for nested subspaces
`A ⊆ B ⊆ D`, orienting `D` from `A`, `B / A` and `D / B` through `B` or through `D / A` gives the
same orientation, since both list a basis of `A`, then lifts of one of `B / A`, then lifts of one of
`D / B`. For the split sequence `A → A × C → C` the induced orientation is the product orientation
(`Orientation.shortExact_inl_snd`). Together these describe products with a fixed factor `Z`: the
orientation `[Z][B]` is induced through `Z × A ⊆ Z × B` by `[Z][A]` and `[C]`
(`Orientation.prod_shortExact_right`), while `[B][Z]` is induced through `A × Z ⊆ B × Z` by
`[A][Z]` and `[C]` up to the sign `(-1) ^ (dim C · dim Z)` of moving `C` past `Z`
(`Orientation.prod_shortExact_left`).

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
* `Orientation.shortExact_inl_snd`: for a split sequence the induced orientation is the product
  orientation.
* `Orientation.shortExact_assoc`: associativity of subspace-first orientations for nested
  subspaces.
* `Orientation.prod_shortExact_right`, `Orientation.prod_shortExact_left`: products of an induced
  orientation with an orientation of a further factor.

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

/-! ### Split sequences, nested sequences and products with a factor -/

namespace Orientation

variable {K A B C D E F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
  [AddCommGroup D] [Module K D] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K A] [FiniteDimensional K C] {a c e : ℕ}

/-- For the split exact sequence `0 → A → A × C → C → 0`, the subspace-first orientation is the
product orientation. -/
@[simp]
theorem shortExact_inl_snd (o : Orientation K A (Fin a)) (p : Orientation K C (Fin c))
    (ha : finrank K A = a) (hc : finrank K C = c) :
    shortExact LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective o p ha hc =
      prod o p ha hc := by
  set b := finBasisOfFinrankEq K A ha
  set e := finBasisOfFinrankEq K C hc
  have hbase : shortExact LinearMap.inl_injective Function.Exact.inl_snd
      LinearMap.snd_surjective b.orientation e.orientation ha hc =
      prod b.orientation e.orientation ha hc := by
    rw [prod_basis_orientation]
    exact shortExact_basis_orientation _ _ _ ha hc b e _ (fun i ↦ by simp [Basis.prod_apply])
      (fun j ↦ by simp [Basis.prod_apply])
  rcases o.eq_or_eq_neg b.orientation (by rw [Fintype.card_fin, ha]) with rfl | rfl <;>
  rcases p.eq_or_eq_neg e.orientation (by rw [Fintype.card_fin, hc]) with rfl | rfl <;>
  simp only [shortExact_neg_left, shortExact_neg_right, prod_neg_left, prod_neg_right, hbase]

/-- Recasting the index type of the subspace orientation along `a = a'` recasts that of the
induced orientation. -/
theorem shortExact_reindex_finCongr_left {f : A →ₗ[K] B} {g : B →ₗ[K] C}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) {a' : ℕ}
    (h : a = a') (o : Orientation K A (Fin a)) (p : Orientation K C (Fin c))
    (ha : finrank K A = a') (hc : finrank K C = c) :
    shortExact hf hfg hg (reindex K A (finCongr h) o) p ha hc =
      reindex K B (finCongr (by rw [h])) (shortExact hf hfg hg o p (ha.trans h.symm) hc) := by
  subst h
  simp only [finCongr_refl, reindex_refl, Equiv.refl_apply]

/-- Recasting the index type of the quotient orientation along `c = c'` recasts that of the
induced orientation. -/
theorem shortExact_reindex_finCongr_right {f : A →ₗ[K] B} {g : B →ₗ[K] C}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) {c' : ℕ}
    (h : c = c') (o : Orientation K A (Fin a)) (p : Orientation K C (Fin c))
    (ha : finrank K A = a) (hc : finrank K C = c') :
    shortExact hf hfg hg o (reindex K C (finCongr h) p) ha hc =
      reindex K B (finCongr (by rw [h])) (shortExact hf hfg hg o p ha (hc.trans h.symm)) := by
  subst h
  simp only [finCongr_refl, reindex_refl, Equiv.refl_apply]

variable [FiniteDimensional K B] [FiniteDimensional K E] [FiniteDimensional K F]

/-- **Associativity of subspace-first orientations.** Let `0 → A → B → C → 0` and
`0 → B → D → E → 0` be short exact, so that `A ⊆ B ⊆ D`, and let `0 → A → D → F → 0` and
`0 → C → F → E → 0` be short exact sequences compatible with them: `D → F` restricts on `B` to
`B → C → F`, and `D → F → E` is `D → E`. Orienting `D` from `A`, `C` and `E` through `B` or
through `F` gives the same orientation: in both, a positive basis of `D` lists a positive basis of
`A`, then lifts of one of `C`, then lifts of one of `E`. The hypotheses on `A → D → F` follow from
the others (`Function.Exact.comp_of_comp_eq`, `Function.Exact.surjective_of_comp_eq`); they are
taken separately, with `k` any map equal to the composite `A → B → D`, so that the induced
orientations can be stated. -/
theorem shortExact_assoc {f : A →ₗ[K] B} {g : B →ₗ[K] C} {f' : B →ₗ[K] D} {g' : D →ₗ[K] E}
    {k : A →ₗ[K] D} {h : D →ₗ[K] F} {i : C →ₗ[K] F} {j : F →ₗ[K] E}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf' : Function.Injective f') (hfg' : Function.Exact f' g') (hg' : Function.Surjective g')
    (hk : Function.Injective k) (hkh : Function.Exact k h) (hh : Function.Surjective h)
    (hi : Function.Injective i) (hij : Function.Exact i j) (hj : Function.Surjective j)
    (hfk : f' ∘ₗ f = k) (hhi : h ∘ₗ f' = i ∘ₗ g) (hjh : j ∘ₗ h = g')
    (o : Orientation K A (Fin a)) (p : Orientation K C (Fin c)) (r : Orientation K E (Fin e))
    (ha : finrank K A = a) (hc : finrank K C = c) (he : finrank K E = e)
    (hB : finrank K B = a + c) (hF : finrank K F = c + e) :
    shortExact hf' hfg' hg' (shortExact hf hfg hg o p ha hc) r hB he =
      reindex K D (finCongr (add_assoc a c e).symm)
        (shortExact hk hkh hh o (shortExact hi hij hj p r hc he) ha hF) := by
  set bA := finBasisOfFinrankEq K A ha
  set bC := finBasisOfFinrankEq K C hc
  set bE := finBasisOfFinrankEq K E he
  choose tC htC using fun l ↦ hg (bC l)
  choose tE htE using fun l ↦ hg' (bE l)
  have htF (l : Fin e) : j (h (tE l)) = bE l := by
    rw [← htE l, ← hjh, LinearMap.comp_apply]
  -- The subspace-first bases of `B`, `D` and `F`.
  set bB := (Basis.ofExactLift hf hfg bA bC tC htC).reindex finSumFinEquiv
  set bD := (Basis.ofExactLift hf' hfg' bB bE tE htE).reindex finSumFinEquiv
  set bF := (Basis.ofExactLift hi hij bC bE (h ∘ tE) htF).reindex finSumFinEquiv
  have hbase : shortExact hf' hfg' hg' (shortExact hf hfg hg bA.orientation bC.orientation ha hc)
      bE.orientation hB he = reindex K D (finCongr (add_assoc a c e).symm)
        (shortExact hk hkh hh bA.orientation
          (shortExact hi hij hj bC.orientation bE.orientation hc he) ha hF) := by
    rw [shortExact_basis_orientation hf hfg hg ha hc bA bC bB (by simp [bB])
        (by simp [bB, htC]),
      shortExact_basis_orientation hf' hfg' hg' hB he bB bE bD (by simp [bD])
        (by simp [bD, htE]),
      shortExact_basis_orientation hi hij hj hc he bC bE bF (by simp [bF])
        (by simp [bF, htF]),
      shortExact_basis_orientation hk hkh hh ha hF bA bF
        (bD.reindex (finCongr (add_assoc a c e))) (fun l ↦ ?_) (fun l ↦ ?_),
      Basis.orientation_reindex bD, ← reindex_trans]
    · rw [show (finCongr (add_assoc a c e)).trans (finCongr (add_assoc a c e).symm) =
        Equiv.refl _ from Equiv.ext fun _ ↦ Fin.ext rfl, reindex_refl]
      rfl
    · -- The first `a` vectors of `bD` are the images of `bA` in `D`.
      have hl (h' : a + (c + e) = a + c + e) :
          Fin.cast h' (Fin.castAdd (c + e) l) = Fin.castAdd e (Fin.castAdd c l) := Fin.ext rfl
      simp [bD, bB, hl, ← hfk]
    · -- The last `c + e` vectors of `bD` are lifts of the basis `bF` of `F`.
      refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
      · have hl (h' : a + (c + e) = a + c + e) :
            Fin.cast h' (Fin.natAdd a (Fin.castAdd e l)) = Fin.castAdd e (Fin.natAdd a l) :=
          Fin.ext rfl
        simp [bD, bB, bF, hl, ← LinearMap.comp_apply h f', hhi, htC]
      · have hl (h' : a + (c + e) = a + c + e) :
            Fin.cast h' (Fin.natAdd a (Fin.natAdd c l)) = Fin.natAdd (a + c) l :=
          Fin.ext (by simp [Nat.add_assoc])
        simp [bD, bF, hl]
  rcases o.eq_or_eq_neg bA.orientation (by rw [Fintype.card_fin, ha]) with rfl | rfl <;>
  rcases p.eq_or_eq_neg bC.orientation (by rw [Fintype.card_fin, hc]) with rfl | rfl <;>
  rcases r.eq_or_eq_neg bE.orientation (by rw [Fintype.card_fin, he]) with rfl | rfl <;>
  simp only [shortExact_neg_left, shortExact_neg_right, Orientation.reindex_neg, hbase]

/-- **A product with a factor on the left.** For a short exact sequence `0 → A → B → C → 0` and a
space `Z`, the product orientation `[Z][B]` of `Z × B`, with `[B]` induced by `[A]` and `[C]`, is
induced through `0 → Z × A → Z × B → C → 0` by `[Z][A]` and `[C]`. -/
theorem prod_shortExact_right {Z : Type*} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    {f : A →ₗ[K] B} {g : B →ₗ[K] C} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {z : ℕ} (oz : Orientation K Z (Fin z))
    (o : Orientation K A (Fin a)) (p : Orientation K C (Fin c)) (hz : finrank K Z = z)
    (ha : finrank K A = a) (hc : finrank K C = c) (hB : finrank K B = a + c) :
    prod oz (shortExact hf hfg hg o p ha hc) hz hB =
      reindex K (Z × B) (finCongr (add_assoc z a c))
        (shortExact (by
            rw [LinearMap.coe_prodMap, LinearMap.id_coe]
            exact Function.injective_id.prodMap hf) (hfg.id_prodMap Z)
          (by rw [LinearMap.coe_comp]; exact hg.comp LinearMap.snd_surjective) (prod oz o hz ha)
          p (by rw [finrank_prod, hz, ha]) hc) := by
  have hf' : Function.Injective (LinearMap.id.prodMap f : Z × A →ₗ[K] Z × B) := by
    rw [LinearMap.coe_prodMap, LinearMap.id_coe]
    exact Function.injective_id.prodMap hf
  have hg' : Function.Surjective (g ∘ₗ LinearMap.snd K Z B) := by
    rw [LinearMap.coe_comp]
    exact hg.comp LinearMap.snd_surjective
  have h := shortExact_assoc (f := LinearMap.inl K Z A) (g := LinearMap.snd K Z A)
    (f' := LinearMap.id.prodMap f) (g' := g ∘ₗ LinearMap.snd K Z B) (k := LinearMap.inl K Z B)
    (h := LinearMap.snd K Z B) (i := f) (j := g) LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective hf' (hfg.id_prodMap Z) hg' LinearMap.inl_injective
    Function.Exact.inl_snd
    LinearMap.snd_surjective hf hfg hg (by ext <;> simp) (by ext <;> simp) rfl oz o p hz ha hc
    (by rw [finrank_prod, hz, ha]) hB
  rw [shortExact_inl_snd, shortExact_inl_snd] at h
  rw [h, ← reindex_trans, show (finCongr (add_assoc z a c).symm).trans
    (finCongr (add_assoc z a c)) = Equiv.refl _ from Equiv.ext fun _ ↦ Fin.ext rfl, reindex_refl]
  rfl

/-- **A product with a factor on the right.** For a short exact sequence `0 → A → B → C → 0` and
a space `Z`, the product orientation `[B][Z]` of `B × Z`, with `[B]` induced by `[A]` and `[C]`,
is `(-1) ^ (dim C · dim Z)` times the orientation induced through `0 → A × Z → B × Z → C → 0` by
`[A][Z]` and `[C]`: the lifts of a basis of `C` move past a basis of `Z`. -/
theorem prod_shortExact_left {Z : Type*} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    {f : A →ₗ[K] B} {g : B →ₗ[K] C} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {z : ℕ} (o : Orientation K A (Fin a))
    (p : Orientation K C (Fin c)) (oz : Orientation K Z (Fin z)) (ha : finrank K A = a)
    (hc : finrank K C = c) (hz : finrank K Z = z) (hB : finrank K B = a + c) :
    prod (shortExact hf hfg hg o p ha hc) oz hB hz =
      (-1 : Kˣ) ^ (c * z) • reindex K (B × Z) (finCongr (by omega))
        (shortExact (by
            rw [LinearMap.coe_prodMap, LinearMap.id_coe]
            exact hf.prodMap Function.injective_id) (hfg.prodMap_id Z)
          (by rw [LinearMap.coe_comp]; exact hg.comp LinearMap.fst_surjective) (prod o oz ha hz)
          p (by rw [finrank_prod, ha, hz]) hc) := by
  have hf' : Function.Injective (f.prodMap LinearMap.id : A × Z →ₗ[K] B × Z) := by
    rw [LinearMap.coe_prodMap, LinearMap.id_coe]
    exact hf.prodMap Function.injective_id
  have hg' : Function.Surjective (g ∘ₗ LinearMap.fst K B Z) := by
    rw [LinearMap.coe_comp]
    exact hg.comp LinearMap.fst_surjective
  have hAZ : finrank K (A × Z) = a + z := by rw [finrank_prod, ha, hz]
  -- The inclusion `A → B × Z` is the kernel of `g × id : B × Z → C × Z` and of
  -- `(b, z) ↦ (z, g b) : B × Z → Z × C`.
  set φ := (LinearMap.snd K B Z).prod (g ∘ₗ LinearMap.fst K B Z)
  have hhi₁ : g.prodMap LinearMap.id ∘ₗ LinearMap.inl K B Z = LinearMap.inl K C Z ∘ₗ g := by
    ext <;> simp
  have hjh₁ : LinearMap.snd K C Z ∘ₗ g.prodMap LinearMap.id = LinearMap.snd K B Z := by
    ext <;> simp
  have hhi₂ : φ ∘ₗ f.prodMap LinearMap.id = LinearMap.inl K Z C ∘ₗ LinearMap.snd K A Z := by
    ext <;> simp [φ, hfg.apply_apply_eq_zero]
  have hjh₂ : LinearMap.snd K Z C ∘ₗ φ = g ∘ₗ LinearMap.fst K B Z := by
    ext <;> simp [φ]
  have hk₁ : Function.Injective (LinearMap.inl K B Z ∘ₗ f) := by
    rw [LinearMap.coe_comp]
    exact LinearMap.inl_injective.comp hf
  have hk₂ : Function.Injective (f.prodMap LinearMap.id ∘ₗ LinearMap.inl K A Z) := by
    rw [LinearMap.coe_comp]
    exact hf'.comp LinearMap.inl_injective
  -- Through `C × Z`, the orientation `[B][Z]` is induced by `[A]` and `[C][Z]`.
  have h₁ := shortExact_assoc (f := f) (g := g) (f' := LinearMap.inl K B Z)
    (g' := LinearMap.snd K B Z) (h := g.prodMap LinearMap.id) (i := LinearMap.inl K C Z)
    (j := LinearMap.snd K C Z) hf hfg hg LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective hk₁
    (hfg.comp_of_comp_eq Function.Exact.inl_snd LinearMap.inl_injective hhi₁ hjh₁)
    (Function.Exact.inl_snd.surjective_of_comp_eq hg LinearMap.snd_surjective hhi₁ hjh₁)
    LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective rfl hhi₁ hjh₁ o p oz
    ha hc hz hB (by rw [finrank_prod, hc, hz])
  -- Through `Z × C`, the orientation induced by `[A][Z]` and `[C]` is induced by `[A]` and
  -- `[Z][C]`.
  have h₂ := shortExact_assoc (f := LinearMap.inl K A Z) (g := LinearMap.snd K A Z)
    (f' := f.prodMap LinearMap.id) (g' := g ∘ₗ LinearMap.fst K B Z) (h := φ)
    (i := LinearMap.inl K Z C) (j := LinearMap.snd K Z C) LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective hf' (hfg.prodMap_id Z) hg' hk₂
    (Function.Exact.inl_snd.comp_of_comp_eq (hfg.prodMap_id Z) LinearMap.inl_injective hhi₂ hjh₂)
    (Function.Exact.inl_snd.surjective_of_comp_eq LinearMap.snd_surjective hg' hhi₂ hjh₂)
    LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective rfl hhi₂ hjh₂ o oz p
    ha hz hc hAZ (by rw [finrank_prod, hz, hc])
  -- The exchange `C × Z ≃ Z × C` compares the two quotient maps.
  have hnat := map_shortExact hk₁
    (hfg.comp_of_comp_eq Function.Exact.inl_snd LinearMap.inl_injective hhi₁ hjh₁)
    (Function.Exact.inl_snd.surjective_of_comp_eq hg LinearMap.snd_surjective hhi₁ hjh₁) ha
    (by rw [finrank_prod, hc, hz]) hk₂
    (Function.Exact.inl_snd.comp_of_comp_eq (hfg.prodMap_id Z) LinearMap.inl_injective hhi₂ hjh₂)
    (Function.Exact.inl_snd.surjective_of_comp_eq LinearMap.snd_surjective hg' hhi₂ hjh₂)
    (LinearEquiv.refl K A) (LinearEquiv.refl K (B × Z)) (LinearEquiv.prodComm K C Z)
    (by ext <;> simp) (by ext <;> simp [φ]) o (prod p oz hc hz)
  simp only [shortExact_inl_snd] at h₁ h₂
  rw [map_refl, map_refl, Equiv.refl_apply, Equiv.refl_apply, map_prodComm_prod,
    shortExact_units_smul_right, shortExact_reindex_finCongr_right] at hnat
  rw [h₁, hnat, h₂]
  -- What remains are the recastings of the index types.
  simp only [reindex_units_smul, ← reindex_trans]
  congr 2

end Orientation
