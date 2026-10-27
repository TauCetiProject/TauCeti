/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
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
separating functions on all stages, and these descend to a separating function on the colimit.

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

end Pushout

section Colimit

/-- A directed colimit of `T1` spaces in `TopCat` along injective transition maps is `T1`. -/
theorem t1Space_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J] {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    {c : Cocone F} (hc : IsColimit c) [∀ j, T1Space (F.obj j)] : T1Space c.pt := by
  refine ⟨fun p ↦ (TopCat.isClosed_iff_of_isColimit _ hc _).2 fun j ↦ ?_⟩
  exact (subsingleton_singleton.preimage (injective_ι_of_isColimit hF hc j)).isClosed

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
  -- The compatible separating functions descend to a continuous function `v` on the colimit.
  let d := hc.desc ⟨TopCat.of (ULift.{u} ℝ), NatTrans.ofSequence
    (fun n ↦ TopCat.ofHom ⟨ULift.up ∘ u n, continuous_uliftUp.comp (u n).continuous⟩)
    fun n ↦ by ext x; exact congrArg ULift.up (congrFun (hu' n) x)⟩
  let v : C(c.pt, ℝ) := ⟨fun p ↦ (d p).down, continuous_uliftDown.comp d.hom.continuous⟩
  have hv (n : ℕ) (x : F.obj n) : v (c.ι.app n x) = u n x := by
    simp only [v, ContinuousMap.coe_mk]
    rw [← ConcreteCategory.comp_apply, hc.fac]
    simp [NatTrans.ofSequence_app]
  have hp (p : c.pt) : ∃ n x, c.ι.app n x = p :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) p
  -- The sublevel and superlevel sets at `1 / 2` separate `S` and `T`.
  refine ⟨v ⁻¹' Iio (1 / 2), v ⁻¹' Ioi (1 / 2), isOpen_Iio.preimage v.continuous,
    isOpen_Ioi.preimage v.continuous, fun p hpS ↦ ?_, fun p hpT ↦ ?_,
    (Ioi_disjoint_Iio_same (a := (1 / 2 : ℝ))).symm.preimage v⟩
  · obtain ⟨n, x, rfl⟩ := hp p
    norm_num [hv, (hu n).1 hpS]
  · obtain ⟨n, x, rfl⟩ := hp p
    norm_num [hv, (hu n).2 hpT]

end Colimit

end TauCeti.TopCat
