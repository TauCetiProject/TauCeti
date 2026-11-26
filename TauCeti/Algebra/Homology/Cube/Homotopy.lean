/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.Data.Finset.Basic

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
`c`, where `h` is the reverse saddle map at `c`: on each state the surviving round-trip composite
is either `m ∘ Δ` or `Δ ∘ m`, and in either case equals `X_p + X_q` for the two opposite arcs `p`
and `q` at `c`.

## Main definitions

* `CategoryTheory.Functor.cubeReverseEdgeHom`: the degree-`-1` family of morphisms between signed
  cube complexes induced by reverse-edge maps in direction `c`.
* `CategoryTheory.Functor.IsCubeReverseEdgeCompatible`: commutativity of the reverse-edge maps with
  the cube edges in all directions other than `c` (`Functor.isCubeReverseEdgeCompatible_iff`,
  `Functor.IsCubeReverseEdgeCompatible.comp_map`).
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
      if hc : c ∈ U.val then
        ((-1 : ℤ) ^ #{b ∈ U.val.erase c | b < c}) •
          (eqToHom (congrArg F.obj (insert_erase hc).symm) ≫
            h (U.val.erase c) (notMem_erase c U.val) ≫
            G.cubeComplexι ⟨U.val.erase c, by
              have := card_erase_add_one hc
              have := U.property
              omega⟩)
      else 0
  else 0

/-- The reverse-edge map vanishes outside cochain degree `-1`. -/
@[simp]
lemma cubeReverseEdgeHom_of_ne {i j : ℤ} (hij : j + 1 ≠ i) :
    cubeReverseEdgeHom F G c h i j = 0 :=
  dite_eq_right hij

/-- Transporting the source degree of `cubeReverseEdgeHom` along `XIsoOfEq` shifts its first
degree index. -/
@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_comp_cubeReverseEdgeHom {i i' : ℤ} (hi : i = i') (j : ℤ) :
    (F.cubeComplex.XIsoOfEq hi).hom ≫ cubeReverseEdgeHom F G c h i' j =
      cubeReverseEdgeHom F G c h i j := by
  subst hi
  simp

/-- On a vertex avoiding `c`, the reverse-edge map in direction `c` vanishes. -/
@[reassoc (attr := simp)]
lemma ι_cubeReverseEdgeHom_of_notMem {i j : ℤ} (U : {U : Finset ι // (#U : ℤ) = i})
    (hc : c ∉ U.val) :
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
lemma ι_cubeReverseEdgeHom_insert {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.val) :
    F.cubeComplexι ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ ≫
        cubeReverseEdgeHom F G c h (r + 1) r =
      ((-1 : ℤ) ^ #{b ∈ S.val | b < c}) • (h S.val hc ≫ G.cubeComplexι S) := by
  have hcU : c ∈ insert c S.val := mem_insert_self c S.val
  rw [cubeReverseEdgeHom, dite_eq_left rfl, F.ι_cubeComplexDesc, dite_eq_left hcU]
  have hcard : #{b ∈ (insert c S.val).erase c | b < c} = #{b ∈ S.val | b < c} := by
    rw [erase_insert hc]
  rw [hcard]
  exact congrArg (((-1 : ℤ) ^ #{b ∈ S.val | b < c}) • ·)
    (cubeReverseEdgeHom_congr F G c h (erase_insert hc) hc (notMem_erase c _) S.property _)

/-- Projecting the reverse-edge map in direction `c` onto a vertex containing `c` gives `0`. -/
@[reassoc (attr := simp)]
lemma cubeReverseEdgeHom_π_of_mem {i j : ℤ} (T : {T : Finset ι // (#T : ℤ) = j}) (hc : c ∈ T.val) :
    cubeReverseEdgeHom F G c h i j ≫ G.cubeComplexπ T = 0 := by
  by_cases hij : j + 1 = i
  · subst hij
    refine F.cubeComplex_hom_ext fun U ↦ ?_
    by_cases hcU : c ∈ U.val
    · obtain ⟨S, hcS, rfl⟩ := exists_notMem_insert_eq_of_mem rfl U hcU
      rw [ι_cubeReverseEdgeHom_insert_assoc F G c h S hcS, comp_zero, Preadditive.zsmul_comp,
        Category.assoc, G.cubeComplexι_π_of_ne, comp_zero, smul_zero]
      intro hEq
      exact hcS (congrArg Subtype.val hEq ▸ hc)
    · rw [ι_cubeReverseEdgeHom_of_notMem_assoc F G c h U hcU, zero_comp, comp_zero]
  · rw [cubeReverseEdgeHom_of_ne F G c h hij, zero_comp]

/-- Projecting the reverse-edge map in direction `c` onto a vertex `S` avoiding `c` recovers the
projection onto `insert c S` followed by `h S` with sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
lemma cubeReverseEdgeHom_π_of_notMem {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r})
    (hc : c ∉ S.val) :
    cubeReverseEdgeHom F G c h (r + 1) r ≫ G.cubeComplexπ S =
      ((-1 : ℤ) ^ #{b ∈ S.val | b < c}) •
        (F.cubeComplexπ
            ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ ≫
          h S.val hc) := by
  refine F.cubeComplex_hom_ext fun U ↦ ?_
  by_cases hcU : c ∈ U.val
  · obtain ⟨V, hcV, rfl⟩ := exists_notMem_insert_eq_of_mem rfl U hcU
    rw [ι_cubeReverseEdgeHom_insert_assoc F G c h V hcV, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.assoc]
    by_cases hVS : V = S
    · subst hVS
      rw [G.cubeComplexι_π_self, Category.comp_id, F.cubeComplexι_π_self_assoc]
    · rw [G.cubeComplexι_π_of_ne hVS, comp_zero, smul_zero, F.cubeComplexι_π_of_ne_assoc,
        zero_comp, smul_zero]
      exact fun hins ↦ hVS (Subtype.ext ((insert_right_inj hcV hc).mp (congrArg Subtype.val hins)))
  · rw [ι_cubeReverseEdgeHom_of_notMem_assoc F G c h U hcU, zero_comp, Preadditive.comp_zsmul,
      F.cubeComplexι_π_of_ne_assoc, zero_comp, smul_zero]
    intro hins
    exact hcU (congrArg Subtype.val hins ▸ mem_insert_self c S.val)

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
    by_cases hcU : c ∈ U.val
    · obtain ⟨S, hcS, rfl⟩ := exists_notMem_insert_eq_of_mem rfl U hcU
      rw [ι_cubeReverseEdgeHom_insert_assoc F G c h₁ S hcS, comp_zero, Preadditive.zsmul_comp,
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
    by_cases hcU : c ∈ U.val
    · obtain ⟨S, hcS, rfl⟩ := exists_notMem_insert_eq_of_mem rfl U hcU
      rw [NatTrans.ι_cubeComplexMap_f_assoc, ι_cubeReverseEdgeHom_insert F' G' c h' S hcS,
        ι_cubeReverseEdgeHom_insert_assoc F G c h S hcS, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp, Category.assoc, NatTrans.ι_cubeComplexMap_f]
      dsimp only
      rw [← Category.assoc, hαβ S.val hcS, Category.assoc]
    · rw [NatTrans.ι_cubeComplexMap_f_assoc, ι_cubeReverseEdgeHom_of_notMem F' G' c h' U hcU,
        comp_zero, ι_cubeReverseEdgeHom_of_notMem_assoc F G c h U hcU, zero_comp]
  · rw [cubeReverseEdgeHom_of_ne F' G' c h' hij, cubeReverseEdgeHom_of_ne F G c h hij,
      comp_zero, zero_comp]

section Homotopy

omit [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] in
/-- Compatibility of a reverse-edge family in direction `c` with all other cube directions `a ≠ c`:
around every mixed square on `S` (`c ∉ S`, `a ∉ insert c S`), reversing `c` and then advancing `a`
equals advancing `a` and then reversing `c` (`Functor.isCubeReverseEdgeCompatible_iff`,
`Functor.IsCubeReverseEdgeCompatible.comp_map`). -/
def IsCubeReverseEdgeCompatible (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) : Prop :=
  ∀ (S : Finset ι) (hc : c ∉ S) (a : ι) (ha : a ∉ insert c S),
    h S hc ≫ G.map (homOfLE (S.subset_insert a)) =
      F.map (homOfLE (insert_subset_insert c (S.subset_insert a))) ≫
        h (insert a S) (notMem_insert_of_notMem_insert_swap hc ha)

omit [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] in
/-- Defining characterization of `Functor.IsCubeReverseEdgeCompatible`: every mixed square of a
reverse `c`-edge and a forward `a`-edge (`a ∉ insert c S`) commutes. -/
lemma isCubeReverseEdgeCompatible_iff (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) :
    IsCubeReverseEdgeCompatible F G c h ↔
      ∀ (S : Finset ι) (hc : c ∉ S) (a : ι) (ha : a ∉ insert c S),
        h S hc ≫ G.map (homOfLE (S.subset_insert a)) =
          F.map (homOfLE (insert_subset_insert c (S.subset_insert a))) ≫
            h (insert a S) (notMem_insert_of_notMem_insert_swap hc ha) :=
  Iff.rfl

omit [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] in
/-- Around any mixed square on `S` (`c ∉ S`, `a ∉ insert c S`), a compatible reverse-edge family
commutes with the forward `a`-edge. -/
@[reassoc]
lemma IsCubeReverseEdgeCompatible.comp_map {F G : Finset ι ⥤ C} {c : ι}
    {h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)}
    (hcomp : IsCubeReverseEdgeCompatible F G c h) {S : Finset ι} (hc : c ∉ S) {a : ι}
    (ha : a ∉ insert c S) :
    h S hc ≫ G.map (homOfLE (S.subset_insert a)) =
      F.map (homOfLE (insert_subset_insert c (S.subset_insert a))) ≫
        h (insert a S) (notMem_insert_of_notMem_insert_swap hc ha) :=
  hcomp S hc a ha

/-- On a vertex `S` avoiding `c`, `dNext + prevD` of `cubeReverseEdgeHom` reduces to the single
forward-then-reverse composite `F(S) ⟶ F(insert c S) ⟶ G(S)`: `prevD` vanishes on `S`, and in
`dNext` every edge `S ⟶ insert a S` with `a ≠ c` lands in a vertex still avoiding `c`. -/
@[reassoc]
lemma ι_dNext_add_prevD_cubeReverseEdgeHom_of_notMem (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) {i : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = i}) (hc : c ∉ S.val) :
    F.cubeComplexι S ≫
        (dNext i (cubeReverseEdgeHom F G c h) + prevD i (cubeReverseEdgeHom F G c h)) =
      F.map (homOfLE (S.val.subset_insert c)) ≫ h S.val hc ≫ G.cubeComplexι S := by
  have hrel_next : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
  have hrel_prev : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1
  rw [Preadditive.comp_add, dNext_eq _ hrel_next, prevD_eq _ hrel_prev,
    ι_cubeReverseEdgeHom_of_notMem_assoc F G c h S hc, zero_comp, add_zero,
    F.ι_cubeComplex_d_assoc, Preadditive.sum_comp]
  rw [Finset.sum_eq_single (⟨c, mem_compl.mpr hc⟩ : (S.valᶜ : Finset ι))]
  · rw [Preadditive.zsmul_comp, Category.assoc, ι_cubeReverseEdgeHom_insert,
      Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
      one_smul]
  · rintro ⟨a, ha⟩ - hac
    have hc' : c ∉ insert a S.val := by
      rw [mem_insert, not_or]
      exact ⟨fun hca ↦ hac (Subtype.ext hca.symm), hc⟩
    rw [Preadditive.zsmul_comp, Category.assoc,
      ι_cubeReverseEdgeHom_of_notMem F G c h _ hc', comp_zero, smul_zero]
  · intro hc'
    exact absurd (mem_univ _) hc'

private lemma map_homOfLE_insert_insert_comp_cubeReverseEdgeHom (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) {r : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.val) {a : ι} (ha : a ∉ insert c S.val) :
    F.map (homOfLE ((insert c S.val).subset_insert a)) ≫
        F.cubeComplexι ⟨insert a (insert c S.val), by
          rw [card_insert_of_notMem ha, card_insert_of_notMem hc, Nat.cast_succ, Nat.cast_succ,
            S.property]⟩ ≫
        cubeReverseEdgeHom F G c h (r + 1 + 1) (r + 1) =
      ((-1 : ℤ) ^ #{b ∈ insert a S.val | b < c}) •
        (F.map (homOfLE (insert_subset_insert c (S.val.subset_insert a))) ≫
          h (insert a S.val) (notMem_insert_of_notMem_insert_swap hc ha) ≫
          G.cubeComplexι ⟨insert a S.val, by
            rw [card_insert_of_notMem (fun haS ↦ ha (mem_insert_of_mem haS)), Nat.cast_succ,
              S.property]⟩) := by
  have haS : a ∉ S.val := fun haS ↦ ha (mem_insert_of_mem haS)
  have hc' : c ∉ insert a S.val := notMem_insert_of_notMem_insert_swap hc ha
  have e : insert a (insert c S.val) = insert c (insert a S.val) := insert_comm a c S.val
  let T : {T : Finset ι // (#T : ℤ) = r + 1} :=
    ⟨insert a S.val, by rw [card_insert_of_notMem haS, Nat.cast_succ, S.property]⟩
  have hι : F.cubeComplexι ⟨insert a (insert c S.val), by
        rw [card_insert_of_notMem ha, card_insert_of_notMem hc, Nat.cast_succ, Nat.cast_succ,
          S.property]⟩ =
      eqToHom (congrArg F.obj e) ≫
        F.cubeComplexι
          ⟨insert c T.val, by rw [card_insert_of_notMem hc', Nat.cast_succ, T.property]⟩ :=
    (F.eqToHom_comp_cubeComplexι e _).symm
  have hmap : F.map (homOfLE ((insert c S.val).subset_insert a)) ≫ eqToHom (congrArg F.obj e) =
      F.map (homOfLE (insert_subset_insert c (S.val.subset_insert a))) := by
    rw [← eqToHom_map F e, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)
  rw [hι, ← Category.assoc (F.map _), ← Category.assoc (F.map _), hmap, Category.assoc,
    ι_cubeReverseEdgeHom_insert F G c h T hc', Preadditive.comp_zsmul]

/-- On `insert c S`, applying `d` and then reversing `c` sums over `a ∉ insert c S` and rewrites
each mixed square `insert c S ⟶ insert a (insert c S) ⟶ insert a S` via `hcomp`. -/
private lemma ι_cubeComplex_d_comp_cubeReverseEdgeHom_insert (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) {r : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.val) :
    F.cubeComplexι ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ ≫
        F.cubeComplex.d (r + 1) (r + 1 + 1) ≫
        cubeReverseEdgeHom F G c h (r + 1 + 1) (r + 1) =
      ∑ a : ((insert c S.val)ᶜ : Finset ι),
        ((-1 : ℤ) ^ #{b ∈ insert c S.val | b < a.val} *
          (-1 : ℤ) ^ #{b ∈ insert a.val S.val | b < c}) •
          (h S.val hc ≫ G.map (homOfLE (S.val.subset_insert a.val)) ≫
            G.cubeComplexι ⟨insert a.val S.val, by
              rw [card_insert_of_notMem
                  (fun haS ↦ (mem_compl.mp a.property) (mem_insert_of_mem haS)),
                Nat.cast_succ, S.property]⟩) := by
  rw [F.ι_cubeComplex_d_assoc, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have ha : a.val ∉ insert c S.val := mem_compl.mp a.property
  rw [Preadditive.zsmul_comp, Category.assoc,
    map_homOfLE_insert_insert_comp_cubeReverseEdgeHom F G c h S hc ha, smul_smul,
    hcomp.comp_map_assoc hc ha]

/-- On `insert c S`, reversing `c` and then applying `d` splits into the `c`-edge round-trip
`F(insert c S) ⟶ G(S) ⟶ G(insert c S)` (whose two Koszul signs square to `+1`) plus the sum over
all unaffected directions `a ∉ insert c S`. -/
private lemma ι_cubeReverseEdgeHom_comp_cubeComplex_d_insert (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S)) {r : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.val) :
    F.cubeComplexι ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ ≫
        cubeReverseEdgeHom F G c h (r + 1) r ≫ G.cubeComplex.d r (r + 1) =
      h S.val hc ≫ G.map (homOfLE (S.val.subset_insert c)) ≫
        G.cubeComplexι
          ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ +
      ∑ a : ((insert c S.val)ᶜ : Finset ι),
        ((-1 : ℤ) ^ #{b ∈ S.val | b < c} * (-1 : ℤ) ^ #{b ∈ S.val | b < a.val}) •
          (h S.val hc ≫ G.map (homOfLE (S.val.subset_insert a.val)) ≫
            G.cubeComplexι ⟨insert a.val S.val, by
              rw [card_insert_of_notMem
                  (fun haS ↦ (mem_compl.mp a.property) (mem_insert_of_mem haS)),
                Nat.cast_succ, S.property]⟩) := by
  rw [ι_cubeReverseEdgeHom_insert_assoc F G c h S hc, Preadditive.zsmul_comp, Category.assoc,
    G.ι_cubeComplex_d, Preadditive.comp_sum, Finset.smul_sum]
  let cIdx : (S.valᶜ : Finset ι) := ⟨c, mem_compl.mpr hc⟩
  rw [← Finset.add_sum_erase _ _ (mem_univ cIdx)]
  congr 1
  · simp only [cIdx, Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul]
  · rw [← Finset.sum_coe_sort]
    refine Fintype.sum_equiv
      ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
        (Equiv.subtypeEquivRight fun x ↦ by simp [cIdx, Subtype.ext_iff, and_comm]))
      _ _ fun a ↦ ?_
    simp only [Preadditive.comp_zsmul, smul_smul]
    rfl

/-- On a vertex `insert c S` (`c ∉ S`), when `h` commutes with all unaffected edges, the
contributions of all `a ∉ insert c S` to `dNext` and `prevD` cancel with opposite Koszul signs,
leaving only the reverse-then-forward composite `F(insert c S) ⟶ G(S) ⟶ G(insert c S)`. -/
@[reassoc]
lemma ι_dNext_add_prevD_cubeReverseEdgeHom_insert (F G : Finset ι ⥤ C) (c : ι)
    (h : ∀ (S : Finset ι), c ∉ S → (F.obj (insert c S) ⟶ G.obj S))
    (hcomp : IsCubeReverseEdgeCompatible F G c h) {r : ℤ}
    (S : {S : Finset ι // (#S : ℤ) = r}) (hc : c ∉ S.val) :
    F.cubeComplexι ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ ≫
        (dNext (r + 1) (cubeReverseEdgeHom F G c h) +
          prevD (r + 1) (cubeReverseEdgeHom F G c h)) =
      h S.val hc ≫ G.map (homOfLE (S.val.subset_insert c)) ≫
        G.cubeComplexι
          ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ := by
  have hrel_next : (ComplexShape.up ℤ).Rel (r + 1) (r + 1 + 1) := rfl
  have hrel_prev : (ComplexShape.up ℤ).Rel r (r + 1) := rfl
  -- Expand `dNext` and `prevD` (splitting `prevD` into the `c`-round-trip and `a ∉ insert c S`),
  -- then pair the two sums over `a ∉ insert c S`.
  rw [Preadditive.comp_add, dNext_eq _ hrel_next, prevD_eq _ hrel_prev,
    ι_cubeComplex_d_comp_cubeReverseEdgeHom_insert F G c h hcomp S hc,
    ι_cubeReverseEdgeHom_comp_cubeComplex_d_insert F G c h S hc,
    ← add_assoc, add_comm _ (h S.val hc ≫ _), add_assoc, ← Finset.sum_add_distrib]
  -- Each unaffected direction `a ∉ insert c S` cancels by opposite Koszul signs.
  refine add_eq_left.mpr (Finset.sum_eq_zero fun a _ ↦ ?_)
  have ha : a.val ∉ insert c S.val := mem_compl.mp a.property
  have haS : a.val ∉ S.val := fun haS ↦ ha (mem_insert_of_mem haS)
  have hca : c ≠ a.val := fun hEq ↦ ha (hEq ▸ mem_insert_self c S.val)
  rw [← add_smul, neg_one_pow_card_filter_lt_insert_mul_insert hc haS hca, neg_add_cancel,
    zero_smul]

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
    by_cases hcU : c ∈ U.val
    · obtain ⟨r, rfl⟩ : ∃ r : ℤ, r + 1 = i := ⟨i - 1, sub_add_cancel i 1⟩
      obtain ⟨S, hcS, rfl⟩ := exists_notMem_insert_eq_of_mem rfl U hcU
      rw [NatTrans.ι_cubeComplexMap_f, hφ_insert S.val hcS, Category.assoc,
        ι_dNext_add_prevD_cubeReverseEdgeHom_insert F G c h hcomp S hcS]
    · rw [NatTrans.ι_cubeComplexMap_f, hφ_notMem U.val hcU, Category.assoc,
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
    Homotopy (NatTrans.cubeComplexMap α) (-NatTrans.cubeComplexMap β) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (by rw [sub_neg_eq_add, ← NatTrans.cubeComplexMap_add])).trans
      (cubeReverseEdgeHomotopyZero c h hcomp (α + β) h_notMem h_insert)

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
      cubeReverseEdgeHom F G c h i j := by
  -- `Homotopy.equivSubZero` (`@[expose]`, no `@[simps]`) preserves `.hom` definitionally.
  rw [cubeReverseEdgeHomotopyNeg]
  change ((Homotopy.ofEq _).trans
    (cubeReverseEdgeHomotopyZero c h hcomp (α + β) h_notMem h_insert)).hom i j = _
  rw [Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, Pi.zero_apply, zero_add,
    cubeReverseEdgeHomotopyZero_hom]

end Homotopy

end CategoryTheory.Functor
