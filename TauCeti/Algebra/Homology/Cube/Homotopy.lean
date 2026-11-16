/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.Cube.Basic

import TauCeti.Data.Finset.Basic

/-!
# Reverse-edge homotopies between signed cube complexes

Let `F, G : Finset ι ⥤ C` be commutative cubes indexed by a finite linearly ordered type `ι` in a
preadditive category `C` with finite biproducts, and fix a distinguished coordinate `c : ι`. A
family of morphisms `h S : F(insert c S) ⟶ G(S)` for `c ∉ S`, running backwards along the edges in
direction `c`, assembles into a degree-`-1` family of maps
`CategoryTheory.Functor.cubeReverseEdgeHom F G c h i j : F.cubeComplex.X i ⟶ G.cubeComplex.X j`
between the signed totalizations of `F` and `G`. On a vertex `U` containing `c` it acts by `h` on
`U \ {c}` with the Koszul sign `(-1) ^ #{b ∈ U \ {c} | b < c}`, and on a vertex avoiding `c` it
vanishes.

Two consecutive reverse-edge maps along the same coordinate compose to zero
(`Functor.cubeReverseEdgeHom_comp_cubeReverseEdgeHom`), because the image of the first is supported
on vertices avoiding `c`. When `h` commutes with the cube edges in every direction `a ≠ c`
(`Functor.IsCubeReverseEdgeCompatible`), the Koszul signs make the contributions of all unaffected
edges `a ≠ c` cancel in `d ≫ H + H ≫ d`, leaving only the forward-then-reverse composite
`F(S) ⟶ F(insert c S) ⟶ G(S)` on vertices avoiding `c` and the reverse-then-forward composite
`F(insert c S) ⟶ G(S) ⟶ G(insert c S)` on vertices containing `c`.

In Khovanov homology this produces the chain homotopy sliding a basepoint mark across a crossing
`c`, where `h` is the reverse saddle map at `c` and the two remaining composites are `m ∘ Δ` and
`Δ ∘ m`, whose sum on any state is the sum of the `X` actions on the two opposite arcs at `c`.

## Main definitions

* `CategoryTheory.Functor.cubeReverseEdgeHom`: the degree-`-1` family of morphisms between signed
  cube complexes induced by reverse-edge maps in direction `c`.
* `CategoryTheory.Functor.IsCubeReverseEdgeCompatible`: commutativity of the reverse-edge maps with
  the cube edges in all directions other than `c`.
* `CategoryTheory.Functor.cubeReverseEdgeHomotopyZero`,
  `CategoryTheory.Functor.cubeReverseEdgeHomotopyNeg`: the resulting `Homotopy` witnesses on signed
  cube complexes.

## Main results

* `Functor.ι_cubeReverseEdgeHom_of_notMem`, `Functor.ι_cubeReverseEdgeHom_insert`: action of
  `cubeReverseEdgeHom` on vertex summands.
* `Functor.cubeReverseEdgeHom_comp_cubeReverseEdgeHom`: two consecutive reverse-edge maps along the
  same coordinate compose to zero (`H² = 0`).
* `Functor.cubeComplexMap_f_comp_cubeReverseEdgeHom`: cube morphisms intertwining the `c`-edges
  intertwine `cubeReverseEdgeHom`.
* `Functor.ι_dNext_add_prevD_cubeReverseEdgeHom_of_notMem`,
  `Functor.ι_dNext_add_prevD_cubeReverseEdgeHom_insert`: signed cancellation of all unaffected
  edges `a ≠ c` in `dNext + prevD`.

## References

* M. Khovanov, *Patterns in knot cohomology I*, Experiment. Math. 12 (2003), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

universe w v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {ι : Type w} [Fintype ι] [LinearOrder ι]

section ReverseEdgeHom

variable (F G : Finset ι ⥤ C) (c : ι)
  (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))

/-- The degree-`-1` morphisms between signed cube complexes given by reverse-edge maps in direction
`c`: in degrees `j + 1 = i`, a vertex `U` containing `c` is sent to `U \ {c}` by `h (U \ {c})` with
sign `(-1) ^ #{b ∈ U \ {c} | b < c}`, while vertices avoiding `c` and all other degree pairs are
sent to `0`. It is characterised on summands by `Functor.ι_cubeReverseEdgeHom_of_notMem` and
`Functor.ι_cubeReverseEdgeHom_insert`. -/
def cubeReverseEdgeHom (i j : ℤ) : F.cubeComplex.X i ⟶ G.cubeComplex.X j :=
  if hij : j + 1 = i then
    F.cubeComplexDesc fun U ↦
      if hc : c ∈ U.1 then
        ((-1 : ℤ) ^ #{b ∈ U.1.erase c | b < c}) •
          (eqToHom (congrArg F.obj (insert_erase hc).symm) ≫
            h (U.1.erase c) (notMem_erase c U.1) ≫
            G.cubeComplexι ⟨U.1.erase c, by
              have := card_erase_add_one hc
              have := U.2
              omega⟩)
      else 0
  else 0

/-- The reverse-edge map vanishes outside cochain degree `-1`. -/
lemma cubeReverseEdgeHom_of_ne {i j : ℤ} (hij : j + 1 ≠ i) :
    cubeReverseEdgeHom F G c h i j = 0 :=
  dite_eq_right hij

/-- On a vertex avoiding `c`, the reverse-edge map in direction `c` vanishes. -/
@[reassoc (attr := simp)]
lemma ι_cubeReverseEdgeHom_of_notMem {i j : ℤ} (U : {U : Finset ι // (#U : ℤ) = i})
    (hc : c ∉ U.1) :
    F.cubeComplexι U ≫ cubeReverseEdgeHom F G c h i j = 0 := by
  by_cases hij : j + 1 = i
  · rw [cubeReverseEdgeHom, dite_eq_left hij, F.ι_cubeComplexDesc, dite_eq_right hc]
  · rw [cubeReverseEdgeHom_of_ne F G c h hij, comp_zero]

private lemma cubeReverseEdgeHom_congr {S T : Finset ι} (hTS : T = S) (hcS : c ∉ S) (hcT : c ∉ T)
    {r : ℤ} (hS : (#S : ℤ) = r) (hT : (#T : ℤ) = r) :
    eqToHom (congrArg F.obj (congrArg (insert c) hTS.symm)) ≫
        h T hcT ≫ G.cubeComplexι ⟨T, hT⟩ =
      h S hcS ≫ G.cubeComplexι ⟨S, hS⟩ := by
  subst hTS
  simp

/-- On the vertex `insert c S` (with `c ∉ S` of height `r`), the reverse-edge map in direction `c`
acts as `h S` into the vertex `S` with Koszul sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
lemma ι_cubeReverseEdgeHom_insert {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.1) :
    F.cubeComplexι ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ ≫
        cubeReverseEdgeHom F G c h (r + 1) r =
      ((-1 : ℤ) ^ #{b ∈ S.1 | b < c}) • (h S.1 hc ≫ G.cubeComplexι S) := by
  have hcU : c ∈ insert c S.1 := mem_insert_self c S.1
  rw [cubeReverseEdgeHom, dite_eq_left rfl, F.ι_cubeComplexDesc, dite_eq_left hcU]
  have hcard : #{b ∈ (insert c S.1).erase c | b < c} = #{b ∈ S.1 | b < c} := by
    rw [erase_insert hc]
  rw [hcard]
  exact congrArg (((-1 : ℤ) ^ #{b ∈ S.1 | b < c}) • ·)
    (cubeReverseEdgeHom_congr F G c h (erase_insert hc) hc (notMem_erase c _) S.2 _)

/-- Projecting the reverse-edge map in direction `c` onto a vertex containing `c` gives `0`. -/
@[reassoc (attr := simp)]
lemma cubeReverseEdgeHom_π_of_mem {i j : ℤ} (T : {T : Finset ι // (#T : ℤ) = j}) (hc : c ∈ T.1) :
    cubeReverseEdgeHom F G c h i j ≫ G.cubeComplexπ T = 0 := by
  by_cases hij : j + 1 = i
  · subst hij
    refine F.cubeComplex_hom_ext fun U ↦ ?_
    by_cases hcU : c ∈ U.1
    · have hcard : (#(U.1.erase c) : ℤ) = j := by
        have := card_erase_add_one hcU
        have := U.2
        omega
      let S : {S : Finset ι // (#S : ℤ) = j} := ⟨U.1.erase c, hcard⟩
      have hcS : c ∉ S.1 := notMem_erase c U.1
      have hU : U = ⟨insert c S.1, by rw [card_insert_of_notMem hcS, Nat.cast_succ, S.2]⟩ :=
        Subtype.ext (insert_erase hcU).symm
      rw [hU, ι_cubeReverseEdgeHom_insert_assoc F G c h S hcS, comp_zero, Preadditive.zsmul_comp,
        Category.assoc, G.cubeComplexι_π_of_ne, comp_zero, smul_zero]
      intro hEq
      exact hcS (congrArg Subtype.val hEq ▸ hc)
    · rw [ι_cubeReverseEdgeHom_of_notMem_assoc F G c h U hcU, zero_comp, comp_zero]
  · rw [cubeReverseEdgeHom_of_ne F G c h hij, zero_comp]

/-- Projecting the reverse-edge map in direction `c` onto a vertex `S` avoiding `c` recovers the
projection onto `insert c S` followed by `h S` with sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
lemma cubeReverseEdgeHom_π_of_notMem {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.1) :
    cubeReverseEdgeHom F G c h (r + 1) r ≫ G.cubeComplexπ S =
      ((-1 : ℤ) ^ #{b ∈ S.1 | b < c}) •
        (F.cubeComplexπ ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ ≫
          h S.1 hc) := by
  refine F.cubeComplex_hom_ext fun U ↦ ?_
  by_cases hcU : c ∈ U.1
  · have hcard : (#(U.1.erase c) : ℤ) = r := by
      have := card_erase_add_one hcU
      have := U.2
      omega
    let V : {V : Finset ι // (#V : ℤ) = r} := ⟨U.1.erase c, hcard⟩
    have hcV : c ∉ V.1 := notMem_erase c U.1
    have hU : U = ⟨insert c V.1, by rw [card_insert_of_notMem hcV, Nat.cast_succ, V.2]⟩ :=
      Subtype.ext (insert_erase hcU).symm
    rw [hU, ι_cubeReverseEdgeHom_insert_assoc F G c h V hcV, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc]
    by_cases hVS : V = S
    · subst hVS
      rw [G.cubeComplexι_π_self, Category.comp_id, F.cubeComplexι_π_self_assoc]
    · rw [G.cubeComplexι_π_of_ne hVS, comp_zero, smul_zero, F.cubeComplexι_π_of_ne_assoc,
        zero_comp, smul_zero]
      intro hins
      apply hVS
      apply Subtype.ext
      have hErase := congrArg (fun X ↦ X.1.erase c) hins
      dsimp only at hErase
      rwa [erase_insert hcV, erase_insert hc] at hErase
  · rw [ι_cubeReverseEdgeHom_of_notMem_assoc F G c h U hcU, zero_comp, Preadditive.comp_zsmul,
      F.cubeComplexι_π_of_ne_assoc, zero_comp, smul_zero]
    intro hins
    exact hcU (congrArg Subtype.val hins ▸ mem_insert_self c S.1)

end ReverseEdgeHom

/-- **Two reverse-edge maps along the same coordinate compose to zero.** The first map lands in
vertices avoiding `c`, on which the second map vanishes. -/
@[reassoc (attr := simp)]
lemma cubeReverseEdgeHom_comp_cubeReverseEdgeHom (F G K : Finset ι ⥤ C) (c : ι)
    (h₁ : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (h₂ : ∀ (S : Finset ι), c ∉ S → (G.obj (insert c S) ⟶ K.obj S))
    (i j l : ℤ) :
    cubeReverseEdgeHom F G c h₁ i j ≫ cubeReverseEdgeHom G K c h₂ j l = 0 := by
  by_cases hij : j + 1 = i
  · subst hij
    refine F.cubeComplex_hom_ext fun U ↦ ?_
    by_cases hcU : c ∈ U.1
    · have hcard : (#(U.1.erase c) : ℤ) = j := by
        have := card_erase_add_one hcU
        have := U.2
        omega
      let S : {S : Finset ι // (#S : ℤ) = j} := ⟨U.1.erase c, hcard⟩
      have hcS : c ∉ S.1 := notMem_erase c U.1
      have hU : U = ⟨insert c S.1, by rw [card_insert_of_notMem hcS, Nat.cast_succ, S.2]⟩ :=
        Subtype.ext (insert_erase hcU).symm
      rw [hU, ι_cubeReverseEdgeHom_insert_assoc F G c h₁ S hcS, comp_zero, Preadditive.zsmul_comp,
        Category.assoc, ι_cubeReverseEdgeHom_of_notMem G K c h₂ S hcS, comp_zero, smul_zero]
    · rw [ι_cubeReverseEdgeHom_of_notMem_assoc F G c h₁ U hcU, zero_comp, comp_zero]
  · rw [cubeReverseEdgeHom_of_ne F G c h₁ hij, zero_comp]

/-- Maps of cubes intertwine reverse-edge maps whenever they intertwine the vertex morphisms along
every `c`-edge. -/
@[reassoc]
lemma cubeComplexMap_f_comp_cubeReverseEdgeHom {F F' G G' : Finset ι ⥤ C} (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (h' : ∀ (S : Finset ι), c ∉ S → (F'.obj (insert c S) ⟶ G'.obj S))
    (α : F ⟶ F') (β : G ⟶ G')
    (hαβ : ∀ (S : Finset ι) (hc : c ∉ S), α.app (insert c S) ≫ h' S hc = h S hc ≫ β.app S)
    (i j : ℤ) :
    (NatTrans.cubeComplexMap α).f i ≫ cubeReverseEdgeHom F' G' c h' i j =
      cubeReverseEdgeHom F G c h i j ≫ (NatTrans.cubeComplexMap β).f j := by
  by_cases hij : j + 1 = i
  · subst hij
    refine F.cubeComplex_hom_ext fun U ↦ ?_
    by_cases hcU : c ∈ U.1
    · have hcard : (#(U.1.erase c) : ℤ) = j := by
        have := card_erase_add_one hcU
        have := U.2
        omega
      let S : {S : Finset ι // (#S : ℤ) = j} := ⟨U.1.erase c, hcard⟩
      have hcS : c ∉ S.1 := notMem_erase c U.1
      have hU : U = ⟨insert c S.1, by rw [card_insert_of_notMem hcS, Nat.cast_succ, S.2]⟩ :=
        Subtype.ext (insert_erase hcU).symm
      rw [hU, NatTrans.ι_cubeComplexMap_f_assoc, ι_cubeReverseEdgeHom_insert F' G' c h' S hcS,
        ι_cubeReverseEdgeHom_insert_assoc F G c h S hcS, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp, Category.assoc, NatTrans.ι_cubeComplexMap_f]
      dsimp only
      rw [← Category.assoc, hαβ S.1 hcS, Category.assoc]
    · rw [NatTrans.ι_cubeComplexMap_f_assoc, ι_cubeReverseEdgeHom_of_notMem F' G' c h' U hcU,
        comp_zero, ι_cubeReverseEdgeHom_of_notMem_assoc F G c h U hcU, zero_comp]
  · rw [cubeReverseEdgeHom_of_ne F' G' c h' hij, cubeReverseEdgeHom_of_ne F G c h hij,
      comp_zero, zero_comp]

section Homotopy

omit [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] in
/-- Compatibility of a reverse-edge family in direction `c` with all other cube directions `a ≠ c`:
around every mixed square on `S` (`c ∉ S`, `a ∉ insert c S`), reversing `c` and then advancing `a`
equals advancing `a` and then reversing `c`. -/
def IsCubeReverseEdgeCompatible (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) : Prop :=
  ∀ (S : Finset ι) (hc : c ∉ S) (a : ι) (ha : a ∉ insert c S),
    h S hc ≫ G.map (homOfLE (S.subset_insert a)) =
      F.map (homOfLE (insert_subset_insert c (S.subset_insert a))) ≫
        h (insert a S) (fun hc' ↦ ha (by
          rcases mem_insert.1 hc' with rfl | hmem
          · exact mem_insert_self c S
          · exact absurd hmem hc))

omit [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] in
/-- Compatibility with unaffected edges is the commutativity of all mixed squares `c` and
`a ≠ c`. -/
lemma isCubeReverseEdgeCompatible_def {F G : Finset ι ⥤ C} {c : ι}
    {h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)} :
    IsCubeReverseEdgeCompatible F G c h ↔
      ∀ (S : Finset ι) (hc : c ∉ S) (a : ι) (ha : a ∉ insert c S),
        h S hc ≫ G.map (homOfLE (S.subset_insert a)) =
          F.map (homOfLE (insert_subset_insert c (S.subset_insert a))) ≫
            h (insert a S) (fun hc' ↦ ha (by
              rcases mem_insert.1 hc' with rfl | hmem
              · exact mem_insert_self c S
              · exact absurd hmem hc)) :=
  Iff.rfl

/-- On a vertex `S` avoiding `c`, `dNext + prevD` of `cubeReverseEdgeHom` reduces to the single
forward-then-reverse composite `F(S) ⟶ F(insert c S) ⟶ G(S)`: `prevD` vanishes on `S`, and in
`dNext` every edge `S ⟶ insert a S` with `a ≠ c` lands in a vertex still avoiding `c`. -/
@[reassoc]
lemma ι_dNext_add_prevD_cubeReverseEdgeHom_of_notMem (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) {i : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = i}) (hc : c ∉ S.1) :
    F.cubeComplexι S ≫
        (dNext i (cubeReverseEdgeHom F G c h) + prevD i (cubeReverseEdgeHom F G c h)) =
      F.map (homOfLE (S.1.subset_insert c)) ≫ h S.1 hc ≫ G.cubeComplexι S := by
  have hrel_next : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
  have hrel_prev : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1
  rw [Preadditive.comp_add, dNext_eq _ hrel_next, prevD_eq _ hrel_prev,
    ι_cubeReverseEdgeHom_of_notMem_assoc F G c h S hc, zero_comp, add_zero,
    F.ι_cubeComplex_d_assoc, Preadditive.sum_comp]
  rw [Finset.sum_eq_single (⟨c, mem_compl.2 hc⟩ : (S.1ᶜ : Finset ι))]
  · rw [Preadditive.zsmul_comp, Category.assoc, ι_cubeReverseEdgeHom_insert,
      Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
      one_smul]
  · rintro ⟨a, ha⟩ - hac
    have hc' : c ∉ insert a S.1 := by
      rw [mem_insert, not_or]
      exact ⟨fun hca ↦ hac (Subtype.ext hca.symm), hc⟩
    rw [Preadditive.zsmul_comp, Category.assoc,
      ι_cubeReverseEdgeHom_of_notMem F G c h _ hc', comp_zero, smul_zero]
  · intro hc'
    exact absurd (mem_univ _) hc'

private lemma map_homOfLE_insert_insert_comp_cubeReverseEdgeHom (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) {r : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.1) {a : ι} (ha : a ∉ insert c S.1) :
    F.map (homOfLE ((insert c S.1).subset_insert a)) ≫
        F.cubeComplexι ⟨insert a (insert c S.1), by
          rw [card_insert_of_notMem ha, card_insert_of_notMem hc, Nat.cast_succ, Nat.cast_succ,
            S.2]⟩ ≫
        cubeReverseEdgeHom F G c h (r + 1 + 1) (r + 1) =
      ((-1 : ℤ) ^ #{b ∈ insert a S.1 | b < c}) •
        (F.map (homOfLE (insert_subset_insert c (S.1.subset_insert a))) ≫
          h (insert a S.1) (fun hc' ↦ ha (by
            rcases mem_insert.1 hc' with rfl | hmem
            · exact mem_insert_self c S.1
            · exact absurd hmem hc)) ≫
          G.cubeComplexι ⟨insert a S.1, by
            rw [card_insert_of_notMem (fun haS ↦ ha (mem_insert_of_mem haS)), Nat.cast_succ,
              S.2]⟩) := by
  have haS : a ∉ S.1 := fun haS ↦ ha (mem_insert_of_mem haS)
  have hc' : c ∉ insert a S.1 := fun hc' ↦ ha (by
    rcases mem_insert.1 hc' with rfl | hmem
    · exact mem_insert_self c S.1
    · exact absurd hmem hc)
  have e : insert a (insert c S.1) = insert c (insert a S.1) := insert_comm a c S.1
  let T : {T : Finset ι // (#T : ℤ) = r + 1} :=
    ⟨insert a S.1, by rw [card_insert_of_notMem haS, Nat.cast_succ, S.2]⟩
  have hι : F.cubeComplexι ⟨insert a (insert c S.1), by
        rw [card_insert_of_notMem ha, card_insert_of_notMem hc, Nat.cast_succ, Nat.cast_succ,
          S.2]⟩ =
      eqToHom (congrArg F.obj e) ≫
        F.cubeComplexι ⟨insert c T.1, by rw [card_insert_of_notMem hc', Nat.cast_succ, T.2]⟩ :=
    (F.eqToHom_comp_cubeComplexι e _).symm
  have hmap : F.map (homOfLE ((insert c S.1).subset_insert a)) ≫ eqToHom (congrArg F.obj e) =
      F.map (homOfLE (insert_subset_insert c (S.1.subset_insert a))) := by
    rw [← eqToHom_map F e, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)
  rw [hι, ← Category.assoc (F.map _), ← Category.assoc (F.map _), hmap, Category.assoc,
    ι_cubeReverseEdgeHom_insert F G c h T hc', Preadditive.comp_zsmul]

omit [Fintype ι] in
private lemma neg_one_pow_insert_cancel {S : Finset ι} {c a : ι} (hc : c ∉ S)
    (ha : a ∉ insert c S) :
    (-1 : ℤ) ^ #{b ∈ insert c S | b < a} * (-1 : ℤ) ^ #{b ∈ insert a S | b < c} +
      (-1 : ℤ) ^ #{b ∈ S | b < c} * (-1 : ℤ) ^ #{b ∈ S | b < a} = 0 := by
  have haS : a ∉ S := fun haS ↦ ha (mem_insert_of_mem haS)
  have hc' : c ∉ insert a S := fun hc' ↦ ha (by
    rcases mem_insert.1 hc' with rfl | hmem
    · exact mem_insert_self c S
    · exact absurd hmem hc)
  have h1 : {b ∈ insert c (insert a S) | b < a} = {b ∈ insert c S | b < a} := by
    ext x
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | rfl | hx, hxa⟩
      · exact ⟨.inl rfl, hxa⟩
      · exact absurd hxa (lt_irrefl _)
      · exact ⟨.inr hx, hxa⟩
    · rintro ⟨rfl | hx, hxa⟩
      · exact ⟨.inl rfl, hxa⟩
      · exact ⟨.inr (.inr hx), hxa⟩
  have h2 : {b ∈ insert a S | b < a} = {b ∈ S | b < a} := by
    ext x
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hx, hxa⟩
      · exact absurd hxa (lt_irrefl _)
      · exact ⟨hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨.inr hx, hxa⟩
  have hsign := neg_one_pow_card_filter_lt_mul_insert (R := ℤ) hc' (mem_insert_self a S)
  rw [h1, h2, erase_insert haS] at hsign
  rw [mul_comm _ ((-1 : ℤ) ^ #{b ∈ insert a S | b < c}), hsign,
    mul_comm ((-1 : ℤ) ^ #{b ∈ S | b < a}), neg_add_cancel]

/-- On a vertex `insert c S` (`c ∉ S`), when `h` commutes with all unaffected edges, the
contributions of all `a ∉ insert c S` to `dNext` and `prevD` cancel with opposite Koszul signs,
leaving only the reverse-then-forward composite `F(insert c S) ⟶ G(S) ⟶ G(insert c S)`. -/
@[reassoc]
lemma ι_dNext_add_prevD_cubeReverseEdgeHom_insert (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) {r : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.1) :
    F.cubeComplexι ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ ≫
        (dNext (r + 1) (cubeReverseEdgeHom F G c h) +
          prevD (r + 1) (cubeReverseEdgeHom F G c h)) =
      h S.1 hc ≫ G.map (homOfLE (S.1.subset_insert c)) ≫
        G.cubeComplexι ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ := by
  have hrel_next : (ComplexShape.up ℤ).Rel (r + 1) (r + 1 + 1) := rfl
  have hrel_prev : (ComplexShape.up ℤ).Rel r (r + 1) := rfl
  rw [Preadditive.comp_add, dNext_eq _ hrel_next, prevD_eq _ hrel_prev]
  have hdNext :
      F.cubeComplexι ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ ≫
          F.cubeComplex.d (r + 1) (r + 1 + 1) ≫
          cubeReverseEdgeHom F G c h (r + 1 + 1) (r + 1) =
        ∑ a : ((insert c S.1)ᶜ : Finset ι),
          ((-1 : ℤ) ^ #{b ∈ insert c S.1 | b < a.1} *
            (-1 : ℤ) ^ #{b ∈ insert a.1 S.1 | b < c}) •
            (h S.1 hc ≫ G.map (homOfLE (S.1.subset_insert a.1)) ≫
              G.cubeComplexι ⟨insert a.1 S.1, by
                rw [card_insert_of_notMem (fun haS ↦ (mem_compl.1 a.2) (mem_insert_of_mem haS)),
                  Nat.cast_succ, S.2]⟩) := by
    rw [F.ι_cubeComplex_d_assoc, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have ha : a.1 ∉ insert c S.1 := mem_compl.1 a.2
    rw [Preadditive.zsmul_comp, Category.assoc,
      map_homOfLE_insert_insert_comp_cubeReverseEdgeHom F G c h S hc ha, smul_smul,
      ← Category.assoc (h S.1 hc), hcomp S.1 hc a.1 ha, Category.assoc]
  have hprevD :
      F.cubeComplexι ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ ≫
          cubeReverseEdgeHom F G c h (r + 1) r ≫ G.cubeComplex.d r (r + 1) =
        h S.1 hc ≫ G.map (homOfLE (S.1.subset_insert c)) ≫
          G.cubeComplexι ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ +
        ∑ a : ((insert c S.1)ᶜ : Finset ι),
          ((-1 : ℤ) ^ #{b ∈ S.1 | b < c} * (-1 : ℤ) ^ #{b ∈ S.1 | b < a.1}) •
            (h S.1 hc ≫ G.map (homOfLE (S.1.subset_insert a.1)) ≫
              G.cubeComplexι ⟨insert a.1 S.1, by
                rw [card_insert_of_notMem (fun haS ↦ (mem_compl.1 a.2) (mem_insert_of_mem haS)),
                  Nat.cast_succ, S.2]⟩) := by
    rw [ι_cubeReverseEdgeHom_insert_assoc F G c h S hc, Preadditive.zsmul_comp, Category.assoc,
      G.ι_cubeComplex_d, Preadditive.comp_sum, Finset.smul_sum]
    let cIdx : (S.1ᶜ : Finset ι) := ⟨c, mem_compl.2 hc⟩
    rw [← Finset.add_sum_erase _ _ (mem_univ cIdx)]
    congr 1
    · simp only [cIdx, Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_smul]
    · refine Finset.sum_bij
        (fun a ha ↦ (⟨a.1, mem_compl.2 fun hmem ↦ by
          rcases mem_insert.1 hmem with rfl | haS
          · exact (mem_erase.1 ha).1 (Subtype.ext rfl)
          · exact mem_compl.1 a.2 haS⟩ : ((insert c S.1)ᶜ : Finset ι)))
        (fun _ _ ↦ mem_univ _)
        (fun a₁ _ a₂ _ hEq ↦
          Subtype.ext (congrArg (Subtype.val : ((insert c S.1)ᶜ : Finset ι) → ι) hEq))
        (fun b _ ↦ ⟨⟨b.1, mem_compl.2 fun hbS ↦ mem_compl.1 b.2 (mem_insert_of_mem hbS)⟩,
          mem_erase.2 ⟨fun hEq ↦ mem_compl.1 b.2
            (congrArg (Subtype.val : (S.1ᶜ : Finset ι) → ι) hEq ▸ mem_insert_self c S.1),
            mem_univ _⟩, rfl⟩)
        fun a _ ↦ ?_
      simp only [Preadditive.comp_zsmul, smul_smul]
  rw [hdNext, hprevD, ← add_assoc, add_comm _ (h S.1 hc ≫ _), add_assoc, ← Finset.sum_add_distrib]
  suffices hzero :
      (∑ a : ((insert c S.1)ᶜ : Finset ι),
        (((-1 : ℤ) ^ #{b ∈ insert c S.1 | b < a.1} * (-1 : ℤ) ^ #{b ∈ insert a.1 S.1 | b < c}) •
          (h S.1 hc ≫ G.map (homOfLE (S.1.subset_insert a.1)) ≫
            G.cubeComplexι ⟨insert a.1 S.1, by
              rw [card_insert_of_notMem (fun haS ↦ (mem_compl.1 a.2) (mem_insert_of_mem haS)),
                Nat.cast_succ, S.2]⟩) +
        ((-1 : ℤ) ^ #{b ∈ S.1 | b < c} * (-1 : ℤ) ^ #{b ∈ S.1 | b < a.1}) •
          (h S.1 hc ≫ G.map (homOfLE (S.1.subset_insert a.1)) ≫
            G.cubeComplexι ⟨insert a.1 S.1, by
              rw [card_insert_of_notMem (fun haS ↦ (mem_compl.1 a.2) (mem_insert_of_mem haS)),
                Nat.cast_succ, S.2]⟩))) = 0 by
    rw [hzero, add_zero]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [← add_smul, neg_one_pow_insert_cancel hc (mem_compl.1 a.2), zero_smul]

/-- **Null-homotopy of a cube map from reverse-edge maps.** If `h` is a reverse-edge family in
direction `c` commuting with all other edges, and `φ : F ⟶ G` acts on vertices avoiding `c` by the
forward-then-reverse composite along `c` and on vertices `insert c S` by the reverse-then-forward
composite along `c`, then `Functor.cubeReverseEdgeHom F G c h` is a chain null-homotopy of
`NatTrans.cubeComplexMap φ`. -/
def cubeReverseEdgeHomotopyZero {F G : Finset ι ⥤ C} (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) (φ : F ⟶ G)
    (hφ_notMem : ∀ (S : Finset ι) (hc : c ∉ S),
      φ.app S = F.map (homOfLE (S.subset_insert c)) ≫ h S hc)
    (hφ_insert : ∀ (S : Finset ι) (hc : c ∉ S),
      φ.app (insert c S) = h S hc ≫ G.map (homOfLE (S.subset_insert c))) :
    Homotopy (NatTrans.cubeComplexMap φ) 0 where
  hom := cubeReverseEdgeHom F G c h
  zero i j hij := cubeReverseEdgeHom_of_ne F G c h hij
  comm i := by
    rw [HomologicalComplex.zero_f, add_zero]
    refine F.cubeComplex_hom_ext fun U ↦ ?_
    by_cases hcU : c ∈ U.1
    · obtain ⟨r, hr⟩ : ∃ r : ℤ, r + 1 = i := ⟨i - 1, sub_add_cancel i 1⟩
      subst hr
      have hcard : (#(U.1.erase c) : ℤ) = r := by
        have := card_erase_add_one hcU
        have := U.2
        omega
      let S : {S : Finset ι // (#S : ℤ) = r} := ⟨U.1.erase c, hcard⟩
      have hcS : c ∉ S.1 := notMem_erase c U.1
      have hU : U = ⟨insert c S.1, by rw [card_insert_of_notMem hcS, Nat.cast_succ, S.2]⟩ :=
        Subtype.ext (insert_erase hcU).symm
      rw [hU, NatTrans.ι_cubeComplexMap_f, hφ_insert S.1 hcS, Category.assoc,
        ι_dNext_add_prevD_cubeReverseEdgeHom_insert F G c h hcomp S hcS]
    · rw [NatTrans.ι_cubeComplexMap_f, hφ_notMem U.1 hcU, Category.assoc,
        ι_dNext_add_prevD_cubeReverseEdgeHom_of_notMem F G c h U hcU]

/-- The underlying degree-`-1` maps of `Functor.cubeReverseEdgeHomotopyZero` are
`Functor.cubeReverseEdgeHom`. -/
@[simp]
lemma cubeReverseEdgeHomotopyZero_hom {F G : Finset ι ⥤ C} (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) (φ : F ⟶ G)
    (hφ_notMem : ∀ (S : Finset ι) (hc : c ∉ S),
      φ.app S = F.map (homOfLE (S.subset_insert c)) ≫ h S hc)
    (hφ_insert : ∀ (S : Finset ι) (hc : c ∉ S),
      φ.app (insert c S) = h S hc ≫ G.map (homOfLE (S.subset_insert c))) (i j : ℤ) :
    (cubeReverseEdgeHomotopyZero c h hcomp φ hφ_notMem hφ_insert).hom i j =
      cubeReverseEdgeHom F G c h i j :=
  (rfl)

/-- **Homotopy `α ≃ -β` of cube maps from reverse-edge maps.** When `α + β : F ⟶ G` equals the
forward-then-reverse composite on vertices avoiding `c` and the reverse-then-forward composite on
vertices `insert c S`, `Functor.cubeReverseEdgeHom F G c h` is a homotopy from
`NatTrans.cubeComplexMap α` to `-NatTrans.cubeComplexMap β`. -/
def cubeReverseEdgeHomotopyNeg {F G : Finset ι ⥤ C} (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) (α β : F ⟶ G)
    (h_notMem : ∀ (S : Finset ι) (hc : c ∉ S),
      α.app S + β.app S = F.map (homOfLE (S.subset_insert c)) ≫ h S hc)
    (h_insert : ∀ (S : Finset ι) (hc : c ∉ S),
      α.app (insert c S) + β.app (insert c S) = h S hc ≫ G.map (homOfLE (S.subset_insert c))) :
    Homotopy (NatTrans.cubeComplexMap α) (-NatTrans.cubeComplexMap β) where
  hom := cubeReverseEdgeHom F G c h
  zero i j hij := cubeReverseEdgeHom_of_ne F G c h hij
  comm i := by
    have hzero := (cubeReverseEdgeHomotopyZero c h hcomp (α + β) h_notMem h_insert).comm i
    have hhom : (cubeReverseEdgeHomotopyZero c h hcomp (α + β) h_notMem h_insert).hom =
        cubeReverseEdgeHom F G c h := rfl
    rw [hhom, NatTrans.cubeComplexMap_add, HomologicalComplex.add_f_apply,
      HomologicalComplex.zero_f, add_zero] at hzero
    rw [HomologicalComplex.neg_f_apply]
    exact eq_add_neg_of_add_eq hzero

/-- The underlying degree-`-1` maps of `Functor.cubeReverseEdgeHomotopyNeg` are
`Functor.cubeReverseEdgeHom`. -/
@[simp]
lemma cubeReverseEdgeHomotopyNeg_hom {F G : Finset ι ⥤ C} (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) (α β : F ⟶ G)
    (h_notMem : ∀ (S : Finset ι) (hc : c ∉ S),
      α.app S + β.app S = F.map (homOfLE (S.subset_insert c)) ≫ h S hc)
    (h_insert : ∀ (S : Finset ι) (hc : c ∉ S),
      α.app (insert c S) + β.app (insert c S) = h S hc ≫ G.map (homOfLE (S.subset_insert c)))
    (i j : ℤ) :
    (cubeReverseEdgeHomotopyNeg c h hcomp α β h_notMem h_insert).hom i j =
      cubeReverseEdgeHom F G c h i j :=
  (rfl)

end Homotopy

end CategoryTheory.Functor
