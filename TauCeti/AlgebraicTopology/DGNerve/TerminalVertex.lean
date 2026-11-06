/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Boundary
public import TauCeti.AlgebraicTopology.DGNerve.Quasicategory
public import TauCeti.AlgebraicTopology.Quasicategory.TerminalVertex
import TauCeti.Data.Finset.Basic

/-!
# Terminal vertices of the differential graded nerve

A vertex `Y` of the differential graded nerve `N_dg(C)` of a dg category `C` is terminal exactly
when every Hom complex `Hom_C(X, Y)` is acyclic in all degrees `d ≤ 0`. These are the degrees whose
cohomology gives the homotopy groups `π_{-d}` of the mapping spaces of `N_dg(C)` (Lurie, *Higher
Algebra*, Remark 1.3.1.12), so the criterion is the dg form of the contractibility of all mapping
spaces into `Y`. In particular an object whose incoming Hom complexes vanish, such as the zero
complex in a dg category of cochain complexes, is a terminal vertex; this gives the terminal half of
the zero objects of the `∞`-categories presented by dg categories of complexes.

A map `∂Δ[n + 1] ⟶ N_dg(C)` amounts to coherences on all proper subsets of the vertices
satisfying the dg nerve equation (`TauCeti.DGNerve.exists_coherences_of_faces` and
`TauCeti.DGNerve.Coherences.boundaryHom`). It extends to `Δ[n + 1]` exactly when the obstruction,
the right-hand side of the dg nerve equation for the one missing coherence, a cycle of degree
`1 - n` in `Hom_C(X 0, X (n + 1))`, is a boundary
(`TauCeti.DGNerve.Coherences.exists_simplex_iff_of_boundary`). Every cycle `z` of degree `-m` in
`Hom_C(X, Y)` arises up to the sign `(-1) ^ (m + 1)` as such an obstruction, for a map out of
`∂Δ[m + 2]` with vertices `X, Y, …, Y`.

## Main results

* `TauCeti.dgNerve.isTerminalVertex_iff`: the vertex at `Y` is terminal if and only if
  `Hom_C(X, Y)` is exact in every degree `d ≤ 0`, for every object `X`.
* `TauCeti.dgNerve.isTerminalVertex_of_isZero`: an object all of whose incoming Hom complexes
  vanish is a terminal vertex.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.12.
* J. Lurie, *Higher Topos Theory*, §1.2.12.
-/

public section

open CategoryTheory Limits Finset Simplicial SSet

namespace TauCeti

open DGNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

namespace dgNerve

/-- The last vertex of a map `∂Δ[n + 1] ⟶ N_dg(C)` is the last vertex of its face `0`. -/
private lemma obj_last_of_map_const {n : ℕ} (σ₀ : (∂Δ[n + 1] : SSet) ⟶ dgNerve R C) {Y : C}
    (hσ₀ : (dgNerve R C).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op
      (SSet.yonedaEquiv (boundary.ι 0 ≫ σ₀)) = (dgNerveEquiv R C).symm Y) :
    Simplex.obj (R := R) (SSet.yonedaEquiv (boundary.ι 0 ≫ σ₀)) (Fin.last n) = Y := by
  refine (congrArg (fun x : Simplex R C 0 ↦ x.obj 0) hσ₀).trans ?_
  simp

/-- If every Hom complex into `Y` is exact in all degrees `d ≤ 0`, the vertex at `Y` is
terminal. -/
private theorem isTerminalVertex_of_exactAt {Y : C}
    (h : ∀ (X : C) (d : ℤ), d ≤ 0 → (dgHomComplex R X Y).ExactAt d) :
    (dgNerve R C).IsTerminalVertex ((dgNerveEquiv R C).symm Y) := by
  rw [SSet.isTerminalVertex_iff]
  intro n σ₀ hσ₀
  have hY := obj_last_of_map_const σ₀ hσ₀
  obtain _ | m := n
  · -- A map `∂Δ[1] ⟶ N_dg(C)` extends by the zero morphism.
    let X₀ := Simplex.obj (R := R) (SSet.yonedaEquiv (boundary.ι 1 ≫ σ₀)) 0
    let e : (dgNerve R C) _⦋1⦌ := Simplex.edge (0 : dgCycles R X₀ Y)
    refine ⟨SSet.yonedaEquiv.symm e, (boundary.eq_ι_comp_iff _ _).2 fun j ↦ ?_⟩
    rw [Equiv.apply_symm_apply]
    refine Simplex.ext_zero ?_
    fin_cases j
    · exact hY
    · rfl
  -- Glue the faces of `σ₀` to coherences on its vertices.
  obtain ⟨f, hself, heq, hfaces⟩ := DGNerve.exists_coherences_of_faces (R := R) (fun _ ↦ True)
    (fun i ↦ Simplex.obj (R := R) (σ₀.app _ (boundary.vertex (m + 1) i)) 0)
    (fun l _ ↦ SSet.yonedaEquiv (boundary.ι l ≫ σ₀)) (fun l _ p ↦ obj_yonedaEquiv_ι_comp σ₀ l p)
    (fun _ _ _ _ hab ↦ map_yonedaEquiv_ι_comp σ₀ hab)
  have hself' := fun i ↦ hself i ((exists_ne i).imp fun _ hl ↦ ⟨trivial, hl⟩)
  have heq' : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) → _ :=
    fun i j S d hij hS hd hl ↦ heq i j S d hij hS hd (hl.imp fun _ hl ↦ ⟨trivial, hl⟩)
  have hd : (-(m + 1 : ℕ) : ℤ) + #(Ioo 0 (Fin.last (m + 2))) = 0 := by simp
  -- The last vertex is `Y`, so the obstruction to filling is a cycle of degree `-m` into `Y`,
  -- hence a boundary.
  have hexact := h (Simplex.obj (R := R) (σ₀.app _ (boundary.vertex (m + 1) 0)) 0) _
    (by omega : -(m + 1 : ℕ) + 1 ≤ (0 : ℤ))
  rw [← hY, obj_yonedaEquiv_ι_comp, Fin.succAbove_zero, Fin.succ_last] at hexact
  obtain ⟨g, hg⟩ := (exactAt_iff_forall_exists_dgDifferential_eq R).1 hexact _
    (f.dgDifferential_boundary_eq_zero heq' hd)
  obtain ⟨x, hxobj, hxcoh⟩ := (f.exists_simplex_iff_of_boundary hself' heq' hd).2 ⟨g, hg⟩
  let x' : (dgNerve R C) _⦋m + 2⦌ := x
  refine ⟨SSet.yonedaEquiv.symm x', (boundary.eq_ι_comp_iff _ _).2 fun l ↦ ?_⟩
  rw [Equiv.apply_symm_apply, dgNerve_δ]
  exact (hfaces x hxobj (fun i j S d hij hS hd ⟨l, _, hl⟩ ↦ hxcoh i j S d hij hS hd ⟨l, hl⟩) l
    trivial).symm

/-! ### The sphere attached to a cycle -/

section Sphere

variable {X Y : C} {m : ℕ}

/-- The objects `X, Y, …, Y` of the sphere attached to a cycle of degree `-m` in `Hom_C(X, Y)`. -/
private abbrev sphereObj (X Y : C) (m : ℕ) : Fin (m + 3) → C :=
  Fin.cons X fun _ ↦ Y

/-- The totally degenerate `(m + 1)`-simplex at `Y`. -/
private noncomputable abbrev degenerate (Y : C) (m : ℕ) : Simplex R C (m + 1) :=
  (Simplex.vertex Y : Simplex R C 0).map ⟨fun _ ↦ 0, monotone_const⟩

open Classical in
/-- The coherences out of the first vertex of the sphere attached to a cycle `z`: the identity of
`X`, and `z` on the face opposite to the vertex `1`; all others vanish. -/
private noncomputable def sphereRow (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) (j : Fin (m + 3))
    (S : Finset (Fin (m + 3))) (p : ℤ) : DGHom R p (sphereObj X Y m 0) (sphereObj X Y m j) :=
  Fin.cases (motive := fun j ↦ DGHom R p (sphereObj X Y m 0) (sphereObj X Y m j))
    (if h : p = 0 then castDeg R h.symm (dgId R (sphereObj X Y m 0)) else 0)
    (fun j' ↦ if h : j' = Fin.last (m + 1) ∧ S = (Ioo 0 (Fin.last (m + 2))).erase 1 ∧
      p = -(m + 1 : ℕ) + 1 then castDeg R h.2.2.symm z else 0) j

open Classical in
/-- The coherences of the sphere attached to a cycle `z`: those out of the first vertex are given
by `TauCeti.dgNerve.sphereRow`, and those between the other vertices are those of the totally
degenerate simplex at `Y`. -/
private noncomputable def sphereCoh (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) :
    Coherences R (sphereObj X Y m) := fun i j S p _ _ _ ↦
  Fin.cases (motive := fun i ↦ DGHom R p (sphereObj X Y m i) (sphereObj X Y m j))
    (sphereRow z j S p)
    (fun i' ↦ Fin.cases (motive := fun j ↦ DGHom R p Y (sphereObj X Y m j)) 0
      (fun j' ↦ if h : i' ≤ j' ∧ S.preimage Fin.succ (Fin.succ_injective _).injOn ⊆ Ioo i' j' ∧
          p + #(S.preimage Fin.succ (Fin.succ_injective _).injOn) = 0 then
        (degenerate (R := R) Y m).coh i' j' _ p h.1 h.2.1 h.2.2 else 0) j) i

private lemma sphereRow_zero (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) (S : Finset (Fin (m + 3)))
    (p : ℤ) :
    sphereRow z 0 S p = if h : p = 0 then castDeg R h.symm (dgId R (sphereObj X Y m 0)) else 0 :=
  rfl

open Classical in
private lemma sphereRow_succ (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) (j : Fin (m + 2))
    (S : Finset (Fin (m + 3))) (p : ℤ) :
    sphereRow z j.succ S p = if h : j = Fin.last (m + 1) ∧
      S = (Ioo 0 (Fin.last (m + 2))).erase 1 ∧ p = -(m + 1 : ℕ) + 1 then
        castDeg R h.2.2.symm z else 0 :=
  rfl

private lemma sphereCoh_zero (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) {j : Fin (m + 3)}
    {S : Finset (Fin (m + 3))} {p : ℤ} {hij : 0 ≤ j} {hS : S ⊆ Ioo 0 j} {hp : p + #S = 0} :
    sphereCoh z 0 j S p hij hS hp = sphereRow z j S p :=
  rfl

private lemma sphereRow_eq_zero (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) {t : Fin (m + 3)}
    (ht₀ : t ≠ 0) (htl : t ≠ Fin.last (m + 2)) (S : Finset (Fin (m + 3))) (p : ℤ) :
    sphereRow z t S p = 0 := by
  obtain ⟨t, rfl⟩ := Fin.exists_succ_eq.2 ht₀
  rw [sphereRow_succ]
  refine dite_eq_right fun h ↦ (htl ?_).elim
  rw [h.1, Fin.succ_last]

private lemma dgDifferential_sphereRow (z : DGHom R (-(m + 1 : ℕ) + 1) X Y)
    (hz : dgDifferential R _ z = 0) (j : Fin (m + 3)) (S : Finset (Fin (m + 3))) (p : ℤ) :
    dgDifferential R p (sphereRow z j S p) = 0 := by
  cases j using Fin.cases with
  | zero =>
    rw [sphereRow_zero]
    split_ifs with h
    · exact d_castDeg_dgId R _ h.symm
    · exact map_zero _
  | succ j =>
    rw [sphereRow_succ]
    split_ifs with h
    · obtain ⟨-, -, rfl⟩ := h
      rw [castDeg_self]
      exact hz
    · exact map_zero _

/-- The coherences of the sphere between the vertices other than the first one are those of the
totally degenerate simplex at `Y`. -/
private lemma sphereCoh_comap_succ (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) :
    (sphereCoh z).comap (Fin.strictMono_succ (n := m + 2)) = (degenerate (R := R) Y m).coh := by
  funext i j S p hij hS hp
  have himg : (S.image Fin.succ).preimage Fin.succ (Fin.succ_injective _).injOn = S := by
    ext s
    simp
  rw [Coherences.comap_apply _ _ _ _ _ (Fin.succ_le_succ_iff.2 hij)
    ((Fin.strictMono_succ (n := m + 2)).image_subset_Ioo hS)
    (by rwa [card_image_of_injective _ (Fin.succ_injective _)])]
  -- `sphereCoh` is defined by cases on its vertices, which reduce at successors.
  exact (dite_eq_left ⟨hij, by rwa [himg], by rwa [himg]⟩).trans (Coherences.congr _ himg)

private lemma sphereCoh_self (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) (i : Fin (m + 3)) :
    sphereCoh z i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (sphereObj X Y m i) := by
  cases i using Fin.cases with
  | zero =>
    rw [sphereCoh_zero, sphereRow_zero, dite_eq_left rfl, castDeg_self]
  | succ i =>
    have := congrFun₂ (congrFun₂ (congrFun₂ (congrFun (sphereCoh_comap_succ (R := R) z) i) i ∅) 0
      le_rfl) (empty_subset _) (by simp)
    rw [Coherences.comap_apply _ _ _ _ _ le_rfl (by simp) (by simp)] at this
    exact (Coherences.congr _ (image_empty _)).symm.trans (this.trans (Simplex.coh_self _ i))

/-- The right-hand side of the dg nerve equation for a coherence of the sphere out of the first
vertex only involves its face terms, since the coherences out of the first vertex to an interior
vertex vanish. -/
private lemma boundary_sphereCoh_zero (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) {j : Fin (m + 3)}
    {S : Finset (Fin (m + 3))} {p : ℤ} (hij : 0 ≤ j) (hS : S ⊆ Ioo 0 j) (hp : p + #S = 0) :
    boundary R (sphereCoh z) 0 j S p hij hS hp =
      ∑ t ∈ S.attach, (#{s ∈ S | t.1 ≤ s} : ℤ).negOnePow • sphereRow z j (S.erase t) (p + 1) := by
  rw [boundary_def]
  refine sum_congr rfl fun t _ ↦ ?_
  have ht := mem_Ioo.1 (hS t.2)
  rw [sphereCoh_zero, sphereCoh_zero,
    sphereRow_eq_zero z ht.1.ne' (ht.2.trans_le (Fin.le_last j)).ne, zero_dgComp, smul_zero,
    sub_zero]

/-- The sphere satisfies the dg nerve equation for the coherences out of the first vertex, except
the one through all interior vertices. -/
private lemma dgDifferential_sphereCoh_zero (z : DGHom R (-(m + 1 : ℕ) + 1) X Y)
    (hz : dgDifferential R _ z = 0) {j : Fin (m + 3)} {S : Finset (Fin (m + 3))} {p : ℤ}
    (hij : 0 ≤ j) (hS : S ⊆ Ioo 0 j) (hp : p + #S = 0) (hB : ∃ l, l ≠ 0 ∧ l ≠ j ∧ l ∉ S) :
    dgDifferential R p (sphereCoh z 0 j S p hij hS hp) =
      boundary R (sphereCoh z) 0 j S p hij hS hp := by
  rw [boundary_sphereCoh_zero, sphereCoh_zero, dgDifferential_sphereRow z hz]
  refine (sum_eq_zero fun t _ ↦ ?_).symm
  cases j using Fin.cases with
  | zero => exact absurd (hS t.2) (by simp)
  | succ j =>
    suffices h0 : sphereRow z j.succ (S.erase t) (p + 1) = 0 by
      rw [h0]
      exact smul_zero _
    rw [sphereRow_succ]
    refine dite_eq_right fun h ↦ ?_
    -- The face omitting `t` is the one carrying `z` only if `t = 1` and `S` is the set of all
    -- interior vertices, which is excluded.
    exfalso
    obtain ⟨l, hl₀, hlj, hlS⟩ := hB
    have hj : j.succ = Fin.last (m + 2) := by rw [h.1, Fin.succ_last]
    have htI : t.1 ∈ Ioo 0 (Fin.last (m + 2)) := hj ▸ hS t.2
    have hlI : l ∈ Ioo 0 (Fin.last (m + 2)) :=
      mem_Ioo.2 ⟨Fin.pos_iff_ne_zero.2 hl₀, Fin.lt_last_iff_ne_last.2 (hj ▸ hlj)⟩
    by_cases hlt : l = t
    · exact hlS (hlt ▸ t.2)
    by_cases hl₁ : l = 1
    · refine notMem_erase t.1 S ?_
      rw [h.2.1]
      exact mem_erase.2 ⟨fun ht₁ ↦ hlt (hl₁.trans ht₁.symm), htI⟩
    · exact hlS (mem_of_mem_erase (h.2.1 ▸ mem_erase.2 ⟨hl₁, hlI⟩ :
        l ∈ S.erase t))

/-- The sphere satisfies the dg nerve equation for the coherences between the vertices other than
the first one, since these are the coherences of a simplex. -/
private lemma dgDifferential_sphereCoh_of_ne_zero (z : DGHom R (-(m + 1 : ℕ) + 1) X Y)
    {i j : Fin (m + 3)} {S : Finset (Fin (m + 3))} {p : ℤ} (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hp : p + #S = 0) (hi : i ≠ 0) :
    dgDifferential R p (sphereCoh z i j S p hij hS hp) =
      boundary R (sphereCoh z) i j S p hij hS hp := by
  have he := Fin.strictMono_succ (n := m + 2)
  have hi₀ := Fin.pos_iff_ne_zero.2 hi
  obtain ⟨i, j, S, rfl, rfl, rfl, hij', hS'⟩ := he.exists_image_eq_of_subset_Ioo hij hS
    (Fin.exists_succ_eq.2 hi) (Fin.exists_succ_eq.2 (hi₀.trans_le hij).ne')
    fun s hs ↦ Fin.exists_succ_eq.2 (hi₀.trans (mem_Ioo.1 (hS hs)).1).ne'
  have hp' : p + #S = 0 := by rwa [card_image_of_injective _ he.injective] at hp
  rw [← Coherences.comap_apply (sphereCoh z) he hij' hS' hp',
    ← boundary_comap (sphereCoh z) he hij' hS' hp', sphereCoh_comap_succ]
  exact (degenerate Y m).dgDifferential_coh i j S p hij' hS' hp'

private lemma sphereRow_succ_last (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) :
    sphereRow z (Fin.last (m + 1)).succ ((Ioo 0 (Fin.last (m + 2))).erase 1)
      (-(m + 1 : ℕ) + 1) = z := by
  rw [sphereRow_succ, dite_eq_left ⟨rfl, rfl, rfl⟩, castDeg_self]

private lemma sphereRow_last_of_ne (z : DGHom R (-(m + 1 : ℕ) + 1) X Y) {S : Finset (Fin (m + 3))}
    (hS : S ≠ (Ioo 0 (Fin.last (m + 2))).erase 1) (p : ℤ) :
    sphereRow z (Fin.last (m + 2)) S p = 0 := by
  rw [← Fin.succ_last, sphereRow_succ]
  exact dite_eq_right fun h ↦ (hS h.2.1).elim

/-- **The obstruction to filling the sphere attached to a cycle `z`** is `± z`. -/
private lemma boundary_sphereCoh_top (z : DGHom R (-(m + 1 : ℕ) + 1) X Y)
    (hd : (-(m + 1 : ℕ) : ℤ) + #(Ioo 0 (Fin.last (m + 2))) = 0) :
    boundary R (sphereCoh z) 0 (Fin.last (m + 2)) (Ioo 0 (Fin.last (m + 2))) _ (Fin.zero_le _)
      subset_rfl hd = ((m + 1 : ℕ) : ℤ).negOnePow • z := by
  have h₁ : (1 : Fin (m + 3)) ∈ Ioo 0 (Fin.last (m + 2)) :=
    mem_Ioo.2 ⟨Fin.pos_iff_ne_zero.2 one_ne_zero, Fin.lt_last_iff_ne_last.2 (by
      rw [ne_eq, Fin.ext_iff, Fin.val_one, Fin.val_last]
      omega)⟩
  rw [boundary_sphereCoh_zero, sum_eq_single_of_mem ⟨1, h₁⟩ (mem_attach _ _) fun t _ ht ↦ by
    rw [sphereRow_last_of_ne z (fun h ↦ ht (Subtype.ext ((erase_inj _ t.2).1 h))), smul_zero]]
  have hcard : #{s ∈ Ioo 0 (Fin.last (m + 2)) | (1 : Fin (m + 3)) ≤ s} = m + 1 := by
    rw [filter_true_of_mem fun s hs ↦ Fin.one_le_of_ne_zero (mem_Ioo.1 hs).1.ne']
    omega
  rw [hcard]
  -- `Fin.last (m + 2)` is `(Fin.last (m + 1)).succ` by definition. Rewriting with
  -- `Fin.succ_last` instead is not type correct: the type of the coherence depends on its target
  -- vertex, while the type of `z` does not.
  exact congrArg _ (sphereRow_succ_last z)

end Sphere

/-! ### Filling spheres at a terminal vertex -/

section Faces

variable {m : ℕ} {V : Fin (m + 3) → C}

/-- **Spheres fill at a terminal vertex**: coherences satisfying the dg nerve equation for every
coherence missing some vertex, ending at a terminal vertex, are the coherences on the boundary of a
simplex. -/
private lemma exists_simplex_of_isTerminalVertex (f : Coherences R V)
    (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (V i))
    (heq : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd)
    (hV : (dgNerve R C).IsTerminalVertex ((dgNerveEquiv R C).symm (V (Fin.last (m + 2))))) :
    ∃ x : Simplex R C (m + 2), x.obj = V ∧ ∀ i j S d hij hS hd,
      (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) → x.coh i j S d hij hS hd ≍ f i j S d hij hS hd := by
  let y : Fin (m + 3) → (dgNerve R C) _⦋m + 1⦌ := f.boundaryFace hself heq
  have hι : ∀ l, SSet.yonedaEquiv (boundary.ι l ≫ f.boundaryHom hself heq) = y l := fun l ↦
    (congrArg _ (f.ι_boundaryHom hself heq l)).trans (Equiv.apply_symm_apply _ _)
  obtain ⟨σ, hσ⟩ := (SSet.isTerminalVertex_iff _).1 hV (f.boundaryHom hself heq) (by
    rw [hι]
    refine Simplex.ext_zero ?_
    rw [dgNerveEquiv_symm_apply, Simplex.vertex_obj, dgNerve_map_apply, Simplex.map_obj]
    simp only [Coherences.boundaryFace_obj, Function.comp_apply]
    exact congrArg V (by simp))
  let x : Simplex R C (m + 2) := SSet.yonedaEquiv σ
  have hx : ∀ l, f.boundaryFace hself heq l = x.map (SimplexCategory.δ l).toOrderHom := fun l ↦
    (hι l).symm.trans ((boundary.eq_ι_comp_iff _ _).1 hσ l)
  -- The objects of `x` are those of its faces.
  have hxobj : x.obj = V := funext fun i ↦ by
    obtain ⟨l, hl⟩ := exists_ne i
    obtain ⟨p, rfl⟩ := Fin.exists_succAbove_eq hl.symm
    have h := congrFun (congrArg Simplex.obj (hx l)) p
    rw [Coherences.boundaryFace_obj] at h
    exact h.symm
  refine ⟨x, hxobj, ?_⟩
  -- A coherence missing the vertex `l` is a coherence of the face opposite to `l`.
  rintro i j S d hij hS hd ⟨l, hli, hlj, hlS⟩
  have he := Fin.strictMono_succAbove l
  obtain ⟨i', j', S', rfl, rfl, rfl, hij', hS'⟩ := he.exists_image_eq_of_subset_Ioo hij hS
    (Fin.exists_succAbove_eq (Ne.symm hli)) (Fin.exists_succAbove_eq (Ne.symm hlj))
    fun s hs ↦ Fin.exists_succAbove_eq fun h ↦ hlS (h ▸ hs)
  have hd' : d + #S' = 0 := by rwa [card_image_of_injective _ he.injective] at hd
  refine (heq_of_eq (x.map_coh_of_strictMono (α := (SimplexCategory.δ l).toOrderHom) he hij'
    hS' hd' hS)).symm.trans ?_
  exact (congr_arg_heq (fun s : Simplex R C (m + 1) ↦ s.coh i' j' S' d hij' hS' hd')
    (hx l)).symm.trans (Coherences.boundaryFace_coh _ _ _ _ _ _ _ _ _ _)

end Faces

/-- At a terminal vertex `Y`, every cycle of degree `d ≤ 0` in `Hom_C(X, Y)` is a boundary. -/
private lemma exactAt_of_isTerminalVertex {Y : C}
    (hY : (dgNerve R C).IsTerminalVertex ((dgNerveEquiv R C).symm Y)) (X : C) {d : ℤ}
    (hd : d ≤ 0) : (dgHomComplex R X Y).ExactAt d := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = -(m + 1 : ℕ) + 1 := ⟨(-d).toNat, by omega⟩
  refine (exactAt_iff_forall_exists_dgDifferential_eq R).2 fun z hz ↦ ?_
  have hd : (-(m + 1 : ℕ) : ℤ) + #(Ioo 0 (Fin.last (m + 2))) = 0 := by simp
  have heq : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (sphereCoh z i j S d hij hS hd) =
        boundary R (sphereCoh z) i j S d hij hS hd := by
    intro i j S d hij hS hd hB
    by_cases hi : i = 0
    · subst hi
      exact dgDifferential_sphereCoh_zero z hz hij hS hd hB
    · exact dgDifferential_sphereCoh_of_ne_zero z hij hS hd hi
  -- Fill the sphere attached to `z`; its obstruction `± z` is then a boundary.
  obtain ⟨g, hg⟩ := ((sphereCoh z).exists_simplex_iff_of_boundary (sphereCoh_self z) heq hd).1
    (exists_simplex_of_isTerminalVertex _ (sphereCoh_self z) heq hY)
  rw [boundary_sphereCoh_top] at hg
  have key : ∀ {A B : C} (g : DGHom R (-(m + 1 : ℕ)) A B) (w : DGHom R (-(m + 1 : ℕ) + 1) A B),
      dgDifferential R _ g = ((m + 1 : ℕ) : ℤ).negOnePow • w →
        dgDifferential R _ (((m + 1 : ℕ) : ℤ).negOnePow • g) = w := by
    intro A B g w h
    rw [map_zsmul_unit, h, smul_smul, Int.units_mul_self, one_smul]
  -- The objects of the sphere at its first and last vertices are `X` and `Y` by definition.
  exact ⟨_, key g z hg⟩

/-- **Terminal vertices of the differential graded nerve**: the vertex at `Y` is terminal if and
only if every Hom complex `Hom_C(X, Y)` is exact in all degrees `d ≤ 0`. -/
theorem isTerminalVertex_iff (Y : C) :
    (dgNerve R C).IsTerminalVertex ((dgNerveEquiv R C).symm Y) ↔
      ∀ (X : C) (d : ℤ), d ≤ 0 → (dgHomComplex R X Y).ExactAt d :=
  ⟨fun hY X _ hd ↦ exactAt_of_isTerminalVertex hY X hd, isTerminalVertex_of_exactAt⟩

/-- An object all of whose incoming Hom complexes vanish, such as the zero complex in a dg category
of cochain complexes, is a terminal vertex of the differential graded nerve. -/
theorem isTerminalVertex_of_isZero {Y : C} (h : ∀ X : C, IsZero (dgHomComplex R X Y)) :
    (dgNerve R C).IsTerminalVertex ((dgNerveEquiv R C).symm Y) :=
  (isTerminalVertex_iff Y).2 fun X d _ ↦
    HomologicalComplex.ExactAt.of_isZero ((HomologicalComplex.eval _ _ d).map_isZero (h X))

end dgNerve

end TauCeti
