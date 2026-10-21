/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.UrysohnsLemma
public import TauCeti.Topology.Category.TopCat.DisjointOpens
public import TauCeti.Topology.Category.TopCat.OpenEmbedding
import TauCeti.Topology.TietzeExtension

/-!
# Normality of attaching spaces and of sequential colimits in `TopCat`

Spaces built by attaching along closed subspaces and then passing to a sequential colimit, such as
the skeletal filtration of the realization of a simplicial space, stay normal and `T1`. This file
proves the two steps.

* Attaching. In a pushout square
  ```
       g
    A ───> X
  m │      │ f
    v      v
    B ───> P
       g₂
  ```
  of `TopCat` in which `m` is a closed embedding, so that `P` is the space `X ∪_g B` obtained by
  attaching `B` to `X` along the closed subspace `A`, the space `P` is normal when `X` and `B` are
  (`TauCeti.TopCat.normalSpace_of_isPushout`) and `T1` when they are
  (`TauCeti.TopCat.t1Space_of_isPushout`). The map `f` is then a closed embedding by
  `TauCeti.TopCat.isClosedEmbedding_of_isPushout`, so `X` is a closed subspace of `P`.
* Sequential colimits. If `F : ℕ ⥤ TopCat` has closed embeddings as transition maps and every
  `F.obj n` is normal, its colimit is normal (`TauCeti.TopCat.normalSpace_of_isColimit`). A
  directed colimit of `T1` spaces along injective transition maps is `T1`
  (`TauCeti.TopCat.t1Space_of_isColimit`).

Both normality proofs separate two disjoint closed sets by a continuous real function, built from
Urysohn functions by the Tietze extension theorem. For attaching, a Urysohn function `u` on `X`
separating the traces of the two sets is pulled back to `A` and extended to `B`, with values `0`
and `1` on the traces there (`ContinuousMap.exists_extension_eqOn_const`). The two functions
agree on `A`, so the sublevel and superlevel sets at `1 / 2` glue to disjoint open sets of `P`.
For a sequential colimit the same extension step, applied stage by stage, gives compatible
separating functions on all stages, and their sublevel and superlevel sets are open in the
colimit.

Lindelöf spaces are treated alongside: attaching a Lindelöf space to a Lindelöf space gives a
Lindelöf space (`TauCeti.TopCat.lindelofSpace_of_isPushout`), and the colimit of a countable
diagram of Lindelöf spaces is Lindelöf (`TauCeti.TopCat.lindelofSpace_of_isColimit`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition A.3, that cell complexes are normal, by the same stagewise extension.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, Chapter 1, for adjunction spaces.
-/

public section

open CategoryTheory Limits Topology Set

universe w u

namespace TauCeti.TopCat

section Pushout

variable {A B X P : TopCat.{u}} {g : A ⟶ X} {m : A ⟶ B} {f : X ⟶ P} {g₂ : B ⟶ P}

/-- Attaching a normal space `B` to a normal space `X` along a closed subspace of `B` gives a
normal space: in a pushout square in `TopCat` whose side `m : A ⟶ B` is a closed embedding, the
corner `P` is normal. -/
theorem normalSpace_of_isPushout (sq : IsPushout g m f g₂) (hm : IsClosedEmbedding m)
    [NormalSpace X] [NormalSpace B] : NormalSpace P := by
  refine ⟨fun F G hF hG hFG ↦ ?_⟩
  rw [isClosed_iff_of_isPushout sq] at hF hG
  have hw (a : A) : g₂ (m a) = f (g a) := by
    rw [← ConcreteCategory.comp_apply, ← sq.w, ConcreteCategory.comp_apply]
  -- A Urysohn function `u` on `X`, and an extension `v` of `u ∘ g` along `m` with values `0` and
  -- `1` on the traces of `F` and `G` on `B`.
  obtain ⟨u, hu₀, hu₁, -⟩ := exists_continuous_zero_one_of_isClosed hF.1 hG.1 (hFG.preimage f)
  obtain ⟨v, hvm, hv₀, hv₁⟩ := (u.comp g.hom).exists_extension_eqOn_const hm hF.2 hG.2
    (hFG.preimage g₂) (a := 0) (b := 1) (fun a ha ↦ hu₀ (by simpa [hw] using ha))
    (fun a ha ↦ hu₁ (by simpa [hw] using ha))
  have hvm' (a : A) : v (m a) = u (g a) := congrFun hvm a
  obtain ⟨W, W', hW, hW', hWW', hfW, hfW', hg₂W, hg₂W'⟩ := exists_disjoint_isOpen_of_isPushout sq
    (isOpen_Iio.preimage u.continuous) (isOpen_Ioi.preimage u.continuous)
    ((Ioi_disjoint_Iio_same (a := (1 / 2 : ℝ))).symm.preimage u)
    (isOpen_Iio.preimage v.continuous) (isOpen_Ioi.preimage v.continuous)
    ((Ioi_disjoint_Iio_same (a := (1 / 2 : ℝ))).symm.preimage v)
    (by ext a; simp [hvm']) (by ext a; simp [hvm'])
  have hp (p : P) : (∃ x, f x = p) ∨ ∃ b, g₂ b = p :=
    Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout sq) p
  refine ⟨W, W', hW, hW', fun p hpF ↦ ?_, fun p hpG ↦ ?_, hWW'⟩
  · obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ := hp p
    · rw [← mem_preimage, hfW]
      norm_num [hu₀ hpF]
    · rw [← mem_preimage, hg₂W]
      norm_num [hv₀ hpF]
  · obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ := hp p
    · rw [← mem_preimage, hfW']
      norm_num [hu₁ hpG]
    · rw [← mem_preimage, hg₂W']
      norm_num [hv₁ hpG]

/-- Attaching a `T1` space `B` to a `T1` space `X` along a closed subspace of `B` gives a `T1`
space: in a pushout square in `TopCat` whose side `m : A ⟶ B` is a closed embedding, the corner
`P` is `T1`. -/
theorem t1Space_of_isPushout (sq : IsPushout g m f g₂) (hm : IsClosedEmbedding m) [T1Space X]
    [T1Space B] : T1Space P := by
  have hf := isClosedEmbedding_of_isPushout sq hm
  have sq' := (forget TopCat).map_isPushout sq
  have hw (a : A) : g₂ (m a) = f (g a) := by
    rw [← ConcreteCategory.comp_apply, ← sq.w, ConcreteCategory.comp_apply]
  have hp (p : P) : (∃ x, f x = p) ∨ ∃ b, g₂ b = p ∧ b ∉ range m :=
    Types.eq_or_eq_of_isPushout' sq' p
  refine ⟨fun p ↦ (isClosed_iff_of_isPushout sq _).2
    ⟨(subsingleton_singleton.preimage hf.injective).isClosed, ?_⟩⟩
  obtain ⟨x, rfl⟩ | ⟨b, rfl, hb⟩ := hp p
  · -- The points of `B` over `f x` are the images under `m` of the points of `A` over `x`.
    have hpre : g₂ ⁻¹' {f x} = m '' (g ⁻¹' {x}) := by
      ext b
      refine ⟨fun hb ↦ ?_, ?_⟩
      · obtain ⟨a, rfl, ha⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          ((forget TopCat).map_isPushout sq.flip).isColimit hm.injective b x).1 hb
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        simp only [mem_preimage, mem_singleton_iff] at ha ⊢
        rw [hw, ha]
    rw [hpre]
    exact hm.isClosedMap _ (isClosed_singleton.preimage g.hom.continuous)
  · -- A point of `B` off the range of `m` is the only point of `B` over its image.
    have hb' : g₂ b ∈ (range f)ᶜ := image_compl_range_of_isPushout sq ▸ mem_image_of_mem g₂ hb
    have hoff (b' : B) (hb'' : g₂ b' = g₂ b) : b' ∉ range m := by
      rintro ⟨a, rfl⟩
      exact hb' ⟨g a, (hw a).symm.trans hb''⟩
    have hinj := Types.injOn_compl_range_of_isPushout sq'
    exact Set.Subsingleton.isClosed fun b₁ hb₁ b₂ hb₂ ↦
      (hinj (hoff b₁ hb₁) hb hb₁).trans (hinj (hoff b₂ hb₂) hb hb₂).symm

/-- Attaching a Lindelöf space `B` to a Lindelöf space `X` gives a Lindelöf space: the corner of
a pushout square in `TopCat` is Lindelöf when the two sides opposite the source are. -/
theorem lindelofSpace_of_isPushout (sq : IsPushout g m f g₂) [LindelofSpace X]
    [LindelofSpace B] : LindelofSpace P := by
  have hp (p : P) : (∃ x, f x = p) ∨ ∃ b, g₂ b = p :=
    Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout sq) p
  refine ⟨((isLindelof_range f.hom.continuous).union
    (isLindelof_range g₂.hom.continuous)).of_isClosed_subset isClosed_univ fun p _ ↦ ?_⟩
  obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ := hp p
  exacts [.inl ⟨x, rfl⟩, .inr ⟨b, rfl⟩]

end Pushout

section Colimit

/-- A directed colimit of `T1` spaces in `TopCat` along injective transition maps is `T1`. -/
theorem t1Space_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J] {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    {c : Cocone F} (hc : IsColimit c) [∀ j, T1Space (F.obj j)] : T1Space c.pt := by
  refine ⟨fun p ↦ (TopCat.isClosed_iff_of_isColimit _ hc _).2 fun j ↦ ?_⟩
  have : Nonempty J := ⟨j⟩
  have hinj : Function.Injective (c.ι.app j) := fun x y h ↦ by
    obtain ⟨k, g, hk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget TopCat) hc) x y).1 h
    exact hF (leOfHom g) hk
  exact (subsingleton_singleton.preimage hinj).isClosed

/-- The colimit of a countable diagram of Lindelöf spaces in `TopCat` is Lindelöf. -/
theorem lindelofSpace_of_isColimit {J : Type w} [SmallCategory J] [Countable J]
    {F : J ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c) [∀ j, LindelofSpace (F.obj j)] :
    LindelofSpace c.pt := by
  have hp (p : c.pt) : ∃ j x, c.ι.app j x = p :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) p
  refine ⟨(isLindelof_iUnion fun j ↦ isLindelof_range (c.ι.app j).hom.continuous).of_isClosed_subset
    isClosed_univ fun p _ ↦ ?_⟩
  obtain ⟨j, x, rfl⟩ := hp p
  exact mem_iUnion_of_mem j (mem_range_self x)

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- The colimit of a sequence of normal spaces in `TopCat` whose transition maps are closed
embeddings is normal. -/
theorem normalSpace_of_isColimit
    (hF : ∀ n : ℕ, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (hc : IsColimit c)
    [∀ n, NormalSpace (F.obj n)] : NormalSpace c.pt := by
  refine ⟨fun S T hS hT hST ↦ ?_⟩
  rw [TopCat.isClosed_iff_of_isColimit _ hc] at hS hT
  have hw (n : ℕ) (x : F.obj n) : c.ι.app (n + 1) (F.map (homOfLE n.le_succ) x) = c.ι.app n x := by
    rw [← ConcreteCategory.comp_apply, c.w]
  -- Separating functions on all stages, each extending the previous one, chosen recursively.
  let Sep (n : ℕ) : Type u :=
    {v : C(F.obj n, ℝ) // EqOn v 0 (c.ι.app n ⁻¹' S) ∧ EqOn v 1 (c.ι.app n ⁻¹' T)}
  have hstep (n : ℕ) (v : Sep n) : ∃ w : Sep (n + 1), w.1 ∘ F.map (homOfLE n.le_succ) = v.1 := by
    obtain ⟨w, hwv, hw₀, hw₁⟩ := v.1.exists_extension_eqOn_const (hF n) (hS (n + 1)) (hT (n + 1))
      (hST.preimage _) (a := 0) (b := 1) (fun x hx ↦ v.2.1 (by simpa [hw] using hx))
      (fun x hx ↦ v.2.2 (by simpa [hw] using hx))
    exact ⟨⟨w, hw₀, hw₁⟩, hwv⟩
  obtain ⟨u₀, hu₀, hu₁, -⟩ := exists_continuous_zero_one_of_isClosed (hS 0) (hT 0)
    (hST.preimage (c.ι.app 0))
  let s (n : ℕ) : Sep n := Nat.rec ⟨u₀, hu₀, hu₁⟩ (fun n v ↦ (hstep n v).choose) n
  let u (n : ℕ) : C(F.obj n, ℝ) := (s n).1
  have hu (n : ℕ) : EqOn (u n) 0 (c.ι.app n ⁻¹' S) ∧ EqOn (u n) 1 (c.ι.app n ⁻¹' T) := (s n).2
  have hu' (n : ℕ) : u (n + 1) ∘ F.map (homOfLE n.le_succ) = u n := (hstep n (s n)).choose_spec
  have hp (p : c.pt) : ∃ n x, c.ι.app n x = p :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) p
  -- The separating functions are compatible with all transition maps, so they agree on points
  -- with the same image in the colimit.
  have hcomp {i j : ℕ} (hij : i ≤ j) (x : F.obj i) : u j (F.map (homOfLE hij) x) = u i x := by
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      rw [← homOfLE_comp hij j.le_succ, F.map_comp, ConcreteCategory.comp_apply, ← ih]
      exact congrFun (hu' j) _
  have hinj (k : ℕ) : Function.Injective (c.ι.app k) :=
    (isClosedEmbedding_ι_of_isColimit
      (fun _ _ ↦ isClosedEmbedding_map_of_isWellOrderContinuous F fun j _ ↦ hF j) hc k).injective
  have hu_eq {i j : ℕ} (x : F.obj i) (y : F.obj j) (hxy : c.ι.app i x = c.ι.app j y) :
      u i x = u j y := by
    rw [← hcomp (le_max_left i j) x, ← hcomp (le_max_right i j) y]
    congr 1
    apply hinj (max i j)
    rwa [← ConcreteCategory.comp_apply, c.w, ← ConcreteCategory.comp_apply, c.w]
  -- The sublevel and superlevel sets at `1 / 2` separate `S` and `T`.
  let W : Set c.pt := {p | ∃ n x, c.ι.app n x = p ∧ u n x < 1 / 2}
  let W' : Set c.pt := {p | ∃ n x, c.ι.app n x = p ∧ 1 / 2 < u n x}
  have hpre (k : ℕ) : c.ι.app k ⁻¹' W = u k ⁻¹' Iio (1 / 2) ∧
      c.ι.app k ⁻¹' W' = u k ⁻¹' Ioi (1 / 2) := by
    constructor <;> ext y <;> constructor
    · rintro ⟨n, x, hx, h⟩
      simpa [hu_eq x y hx] using h
    · exact fun h ↦ ⟨k, y, rfl, h⟩
    · rintro ⟨n, x, hx, h⟩
      simpa [hu_eq x y hx] using h
    · exact fun h ↦ ⟨k, y, rfl, h⟩
  refine ⟨W, W', (TopCat.isOpen_iff_of_isColimit _ hc _).2 fun k ↦ ?_,
    (TopCat.isOpen_iff_of_isColimit _ hc _).2 fun k ↦ ?_, fun p hpS ↦ ?_, fun p hpT ↦ ?_, ?_⟩
  · rw [(hpre k).1]
    exact isOpen_Iio.preimage (u k).continuous
  · rw [(hpre k).2]
    exact isOpen_Ioi.preimage (u k).continuous
  · obtain ⟨n, x, rfl⟩ := hp p
    exact ⟨n, x, rfl, by norm_num [(hu n).1 hpS]⟩
  · obtain ⟨n, x, rfl⟩ := hp p
    exact ⟨n, x, rfl, by norm_num [(hu n).2 hpT]⟩
  · refine Set.disjoint_left.2 ?_
    rintro p ⟨n, x, rfl, hx⟩ ⟨n', x', hx', hx''⟩
    rw [hu_eq x' x hx'] at hx''
    exact (lt_asymm hx hx'').elim

end Colimit

end TauCeti.TopCat
