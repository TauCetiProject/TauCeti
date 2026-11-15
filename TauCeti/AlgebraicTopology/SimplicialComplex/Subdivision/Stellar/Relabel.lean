/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
import Mathlib.Data.Set.Card
import TauCeti.SetTheory.Cardinal.Extend

/-!
# Stellar equivalence and relabeling

`PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling` is preserved by injective
relabelings (`StellarEquivalentUpToRelabeling.map`). This file proves the converse for complexes
with finitely many faces: if the images of `K` and `L` under an injective vertex map `f : ι → κ`
are stellar equivalent up to relabeling, then so are `K` and `L`
(`PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_map_iff`). The target type `κ` is
arbitrary, possibly much larger than `ι`; this is what lets combinatorial balls, spheres and
manifolds be recognised after relabeling into sums, as in the join descriptions of stars and
links.

The proof has three steps.

* A stellar move, hence a stellar equivalence, is carried along any vertex map that is injective
  on the finitely many vertices involved (`map_stellarSubdivision_of_injOn` and
  `StellarEquivalent.exists_finite_forall_injOn`). Global injectivity is not needed.
* A chain of common relabelings between finite complexes collapses to a single one
  (`StellarEquivalentUpToRelabeling.exists_stellarEquivalent_map`): consecutive relabelings are
  matched on the finitely many vertices of the middle complex by a permutation of `ι ⊕ ℕ`.
* The single stellar equivalence in `κ ⊕ ℕ` is pulled back to `ι ⊕ ℕ` along a map injective on
  its finitely many vertices.

Finally, a relabeling of a complex inside its own vertex type is a stellar equivalence up to
relabeling (`stellarEquivalentUpToRelabeling_map_self`), so simplex boundaries, and simplices,
on vertex sets of the same size are stellar equivalent up to relabeling.

## Main results

* `PreAbstractSimplicialComplex.StellarEquivalent.exists_finite_forall_injOn`: a stellar
  equivalence from a finite complex is supported on finitely many vertices.
* `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.exists_stellarEquivalent_map`:
  intrinsic stellar equivalence of finite complexes is witnessed by one common relabeling.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_map_iff`: injective relabelings
  reflect intrinsic stellar equivalence of finite complexes.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_simplexBoundary` and
  `stellarEquivalentUpToRelabeling_simplex`: the standard models on vertex sets of equal size
  are intrinsically stellar equivalent.
-/

public section

open Finset Function

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {K L : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι}

/-! ### Relabeling along maps injective on the vertices -/

/-- Every vertex of a stellar subdivision is the new vertex or an old vertex. -/
theorem eq_or_singleton_mem_of_singleton_mem_stellarSubdivision {x : ι}
    (hx : ({x} : Finset ι) ∈ stellarSubdivision K σ v) : x = v ∨ ({x} : Finset ι) ∈ K := by
  by_cases hxv : x = v
  · exact Or.inl hxv
  · exact Or.inr ((mem_stellarSubdivision_iff_of_notMem
      (Finset.notMem_singleton.mpr (Ne.symm hxv))).mp hx).1

/-- A vertex map that is injective on a set containing the vertices of `K`, the starred set and
the new vertex commutes with stellar subdivision. -/
theorem map_stellarSubdivision_of_injOn {S : Set ι} {f : ι → κ} (hf : S.InjOn f)
    (hK : ∀ x, ({x} : Finset ι) ∈ K → x ∈ S) (hσ : ↑σ ⊆ S) (hv : v ∈ S) :
    (stellarSubdivision K σ v).map f = stellarSubdivision (K.map f) (σ.image f) (f v) := by
  classical
  -- Points outside `S` go to a second copy of `ι`, which makes the map injective.
  let g : ι → κ ⊕ ι := fun x => if x ∈ S then Sum.inl (f x) else Sum.inr x
  have hg : Injective g := by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp only [g, hx, hy, ↓reduceIte,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hxy
    · exact hf hx hy hxy
    · exact hxy
  have hgS : ∀ x ∈ S, g x = Sum.inl (f x) := fun x hx => by simp [g, hx]
  have hKg : K.map g = (K.map f).map Sum.inl := by
    rw [map_map]
    exact map_congr fun x hx => hgS x (hK x hx)
  have hσg : σ.image g = (σ.image f).image Sum.inl := by
    rw [Finset.image_image]
    exact Finset.image_congr fun x hx => hgS x (hσ hx)
  apply map_injective (Sum.inl_injective : Injective (Sum.inl : κ → κ ⊕ ι))
  calc ((stellarSubdivision K σ v).map f).map Sum.inl
      = (stellarSubdivision K σ v).map g := by
        rw [map_map]
        refine map_congr fun x hx => (hgS x ?_).symm
        rcases eq_or_singleton_mem_of_singleton_mem_stellarSubdivision hx with rfl | hx
        · exact hv
        · exact hK x hx
    _ = stellarSubdivision (K.map g) (σ.image g) (g v) := map_stellarSubdivision g hg
    _ = (stellarSubdivision (K.map f) (σ.image f) (f v)).map Sum.inl := by
        rw [hKg, hσg, hgS v hv, map_stellarSubdivision Sum.inl Sum.inl_injective]

/-- A vertex map injective on the vertices of both sides carries a stellar move to a stellar
move. -/
theorem IsStellarMove.map_of_injOn {f : ι → κ} (h : IsStellarMove K L)
    (hf : {x | ({x} : Finset ι) ∈ K ∨ ({x} : Finset ι) ∈ L}.InjOn f) :
    IsStellarMove (K.map f) (L.map f) := by
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp h
  have hvL : ({v} : Finset ι) ∈ stellarSubdivision K σ v :=
    singleton_mem_stellarSubdivision_iff.mpr hσ
  refine isStellarMove_iff.mpr ⟨σ.image f, f v, mem_map_iff.mpr ⟨σ, hσ, rfl⟩, fun hfv => ?_,
    map_stellarSubdivision_of_injOn hf (fun x hx => Or.inl hx)
      (fun x hx => Or.inl (singleton_mem_of_mem hσ hx)) (Or.inr hvL)⟩
  obtain ⟨x, hx, hxv⟩ := singleton_mem_map_iff.mp hfv
  rw [hf (Or.inl hx) (Or.inr hvL) hxv] at hx
  exact hv hx

/-- **A stellar equivalence has finite support.** A stellar equivalence starting from a complex
with finitely many faces only involves finitely many vertices, and any vertex map injective on
them carries it to a stellar equivalence of the image complexes. -/
theorem StellarEquivalent.exists_finite_forall_injOn (h : StellarEquivalent K L)
    (hK : K.faces.Finite) :
    ∃ S : Set ι, S.Finite ∧ (∀ x, ({x} : Finset ι) ∈ K → x ∈ S) ∧
      (∀ x, ({x} : Finset ι) ∈ L → x ∈ S) ∧
      ∀ f : ι → κ, S.InjOn f → StellarEquivalent (K.map f) (L.map f) := by
  -- The induction carries the stellar equivalence along, to transfer finiteness.
  refine (h.induction_on (P := fun A B => StellarEquivalent A B ∧ (A.faces.Finite →
      ∃ S : Set ι, S.Finite ∧ (∀ x, ({x} : Finset ι) ∈ A → x ∈ S) ∧
        (∀ x, ({x} : Finset ι) ∈ B → x ∈ S) ∧
        ∀ f : ι → κ, S.InjOn f → StellarEquivalent (A.map f) (B.map f))) ?_ ?_ ?_ ?_).2 hK
  · intro A B hAB
    refine ⟨hAB.stellarEquivalent, fun hA => ?_⟩
    exact ⟨_, (finite_setOf_singleton_mem hA).union
        (finite_setOf_singleton_mem (hAB.finite_faces_iff.mp hA)),
      fun x hx => Or.inl hx, fun x hx => Or.inr hx,
      fun f hf => (hAB.map_of_injOn hf).stellarEquivalent⟩
  · intro A
    exact ⟨.refl A, fun hA => ⟨_, finite_setOf_singleton_mem hA, fun x hx => hx,
      fun x hx => hx, fun f _ => .refl _⟩⟩
  · rintro A B ⟨hAB, ih⟩
    refine ⟨hAB.symm, fun hB => ?_⟩
    obtain ⟨S, hS, hA, hB, hmap⟩ := ih (hAB.finite_faces_iff.mpr hB)
    exact ⟨S, hS, hB, hA, fun f hf => (hmap f hf).symm⟩
  · rintro A B C ⟨hAB, ih₁⟩ ⟨hBC, ih₂⟩
    refine ⟨hAB.trans hBC, fun hA => ?_⟩
    obtain ⟨S, hS, hAS, -, hmap⟩ := ih₁ hA
    obtain ⟨T, hT, -, hCT, hmap'⟩ := ih₂ (hAB.finite_faces_iff.mp hA)
    exact ⟨S ∪ T, hS.union hT, fun x hx => Or.inl (hAS x hx), fun x hx => Or.inr (hCT x hx),
      fun f hf => (hmap f (hf.mono Set.subset_union_left)).trans
        (hmap' f (hf.mono Set.subset_union_right))⟩

/-! ### Collapsing chains of relabelings -/

/-- Relabeling a complex inside its own vertex type is a stellar equivalence up to
relabeling. -/
theorem stellarEquivalentUpToRelabeling_map_self {π : ι → ι} (hπ : Injective π) :
    StellarEquivalentUpToRelabeling K (K.map π) := by
  refine .of_common_relabeling ⟨Sum.inl ∘ π, Sum.inl_injective.comp hπ⟩
    ⟨Sum.inl, Sum.inl_injective⟩ ?_
  rw [map_map]
  exact .refl _

/-- **Intrinsic stellar equivalence of finite complexes is witnessed by a single common
relabeling**: the chain of relabelings in the definition of
`StellarEquivalentUpToRelabeling` can be collapsed to one stellar equivalence in `ι ⊕ ℕ`. -/
theorem StellarEquivalentUpToRelabeling.exists_stellarEquivalent_map
    (h : StellarEquivalentUpToRelabeling K L) (hK : K.faces.Finite) :
    ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (K.map f) (L.map g) := by
  -- The induction carries the equivalence along, to transfer finiteness.
  refine (h.induction_on (P := fun A B => StellarEquivalentUpToRelabeling A B ∧
      (A.faces.Finite → ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (A.map f) (B.map g)))
    ?_ ?_ ?_ ?_).2 hK
  · intro A B f g he
    exact ⟨.of_common_relabeling f g he, fun _ => ⟨f, g, he⟩⟩
  · intro A
    exact ⟨.refl A, fun _ => ⟨⟨Sum.inl, Sum.inl_injective⟩, ⟨Sum.inl, Sum.inl_injective⟩,
      .refl _⟩⟩
  · rintro A B ⟨hAB, ih⟩
    refine ⟨hAB.symm, fun hB => ?_⟩
    obtain ⟨f, g, he⟩ := ih (hAB.finite_faces_iff.mpr hB)
    exact ⟨g, f, he.symm⟩
  · rintro A B C ⟨hAB, ih₁⟩ ⟨hBC, ih₂⟩
    refine ⟨hAB.trans hBC, fun hA => ?_⟩
    obtain ⟨f, g, he⟩ := ih₁ hA
    have hB := hAB.finite_faces_iff.mp hA
    obtain ⟨f', g', he'⟩ := ih₂ hB
    -- A permutation of `ι ⊕ ℕ` moves the copy of `B` along `f'` onto the copy along `g`.
    have hinj : (f' '' {x | ({x} : Finset ι) ∈ B}).InjOn (Function.extend f' g id) := by
      rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
      rw [f'.injective.extend_apply, f'.injective.extend_apply] at hxy
      rw [g.injective hxy]
    obtain ⟨π, hπ⟩ := hinj.exists_equiv_eqOn ((finite_setOf_singleton_mem hB).image f')
    have hBπ : B.map g = (B.map f').map π := by
      rw [map_map]
      exact map_congr fun x hx => by
        rw [comp_apply, hπ (Set.mem_image_of_mem f' hx), f'.injective.extend_apply]
    refine ⟨f, g'.trans π.toEmbedding, he.trans ?_⟩
    have hmove := he'.map π π.injective
    rw [map_map, map_map] at hmove
    rw [hBπ, map_map, Function.Embedding.coe_trans, Equiv.coe_toEmbedding]
    exact hmove

/-! ### Reflection along injective relabelings -/

/-- **Injective relabelings reflect intrinsic stellar equivalence** of finite complexes, for an
arbitrary target type. -/
theorem StellarEquivalentUpToRelabeling.of_map {f : ι → κ} (hf : Injective f)
    (hK : K.faces.Finite) (h : StellarEquivalentUpToRelabeling (K.map f) (L.map f)) :
    StellarEquivalentUpToRelabeling K L := by
  classical
  have hKf : (K.map f).faces.Finite := (finite_faces_map_iff_of_injective f hf).mpr hK
  have hL : L.faces.Finite :=
    (finite_faces_map_iff_of_injective f hf).mp (h.finite_faces_iff.mp hKf)
  obtain ⟨F, G, he⟩ := h.exists_stellarEquivalent_map hKf
  obtain ⟨S, hS, -, hLS, hmap⟩ := he.exists_finite_forall_injOn (κ := ι ⊕ ℕ)
    ((finite_faces_map_iff_of_injective F F.injective).mpr hKf)
  -- `p` sends the copy `F (f x)` of a vertex back to `x`, and the rest of `S` injectively into `ℕ`.
  obtain ⟨p, hpS, hpF⟩ := (F.injective.comp hf).exists_injOn_comp_eq_inl hS
  have hp (x : ι) : p (F (f x)) = Sum.inl x := congrFun hpF x
  have hGS : ∀ y, ({y} : Finset ι) ∈ L → G (f y) ∈ S := fun y hy =>
    hLS _ (by rw [map_map]; exact mem_map_iff.mpr ⟨{y}, hy, by simp⟩)
  -- A permutation `π` of `ι ⊕ ℕ` turns the copy of `L` along `p ∘ G ∘ f` into one along `inl`.
  have hinj : (Sum.inl '' {y | ({y} : Finset ι) ∈ L}).InjOn
      (Sum.elim (p ∘ G ∘ f) Sum.inr) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hyy'
    simp only [Sum.elim_inl, comp_apply] at hyy'
    rw [hf (G.injective (hpS (hGS y hy) (hGS y' hy') hyy'))]
  obtain ⟨π, hπ⟩ := hinj.exists_equiv_eqOn ((finite_setOf_singleton_mem hL).image _)
  have hKp : K.map ((p ∘ F) ∘ f) = K.map Sum.inl := map_congr fun x _ => hp x
  have hLp : L.map ((p ∘ G) ∘ f) = L.map (π ∘ Sum.inl) := map_congr fun y hy =>
    (hπ (Set.mem_image_of_mem _ hy)).symm
  have hpe := hmap p hpS
  rw [map_map, map_map, map_map, map_map, hKp, hLp] at hpe
  exact .of_common_relabeling ⟨Sum.inl, Sum.inl_injective⟩
    ((⟨Sum.inl, Sum.inl_injective⟩ : ι ↪ ι ⊕ ℕ).trans π.toEmbedding) hpe

/-- Injective relabelings preserve and reflect intrinsic stellar equivalence of finite
complexes. -/
theorem stellarEquivalentUpToRelabeling_map_iff {f : ι → κ} (hf : Injective f)
    (hK : K.faces.Finite) :
    StellarEquivalentUpToRelabeling (K.map f) (L.map f) ↔
      StellarEquivalentUpToRelabeling K L :=
  ⟨StellarEquivalentUpToRelabeling.of_map hf hK, fun h => h.map f hf⟩

/-! ### The standard models -/

/-- A vertex set of the same size as `V` is the image of `V` under a permutation. -/
private theorem exists_equiv_image_eq {V W : Finset ι} (h : V.card = W.card) :
    ∃ π : ι ≃ ι, V.image π = W := by
  classical
  cases isEmpty_or_nonempty ι
  · exact ⟨Equiv.refl ι, by simp [Finset.eq_empty_of_isEmpty]⟩
  obtain ⟨φ, hφ⟩ := V.finite_toSet.exists_bijOn_of_encard_eq (t := (W : Set ι))
    (by simp [Set.encard_coe_eq_coe_finsetCard, h])
  obtain ⟨π, hπ⟩ := hφ.injOn.exists_equiv_eqOn V.finite_toSet
  refine ⟨π, Finset.coe_injective ?_⟩
  rw [Finset.coe_image, hπ.image_eq, hφ.image_eq]

/-- Simplex boundaries on vertex sets of the same size are intrinsically stellar equivalent. -/
theorem stellarEquivalentUpToRelabeling_simplexBoundary {V W : Finset ι} (h : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplexBoundary V) (simplexBoundary W) := by
  obtain ⟨π, rfl⟩ := exists_equiv_image_eq h
  have hmap := map_simplexBoundary V π.toEmbedding
  rw [Equiv.coe_toEmbedding] at hmap
  rw [← hmap]
  exact stellarEquivalentUpToRelabeling_map_self π.injective

/-- Simplices on vertex sets of the same size are intrinsically stellar equivalent. -/
theorem stellarEquivalentUpToRelabeling_simplex {V W : Finset ι} (h : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplex V) (simplex W) := by
  obtain ⟨π, rfl⟩ := exists_equiv_image_eq h
  rw [← map_simplex]
  exact stellarEquivalentUpToRelabeling_map_self π.injective

end PreAbstractSimplicialComplex
