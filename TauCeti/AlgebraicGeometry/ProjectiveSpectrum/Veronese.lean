/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Veronese

/-!
# The projective spectrum of a Veronese subalgebra

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra and `d ≠ 0`. The Veronese subalgebra
`A^{(d)} = ⨁ₖ 𝒜 (d k)` has the same projective spectrum as `A`:

`Proj A^{(d)} ≅ Proj A`.

Both schemes are covered by the standard charts of the homogeneous elements `f ∈ 𝒜 (d k)`,
`k > 0`: for `Proj A^{(d)}` these are all its standard charts, and for `Proj A` they suffice
because `D₊(a) = D₊(aᵈ)`. On such a chart the isomorphism is `Spec` of the identification
`A^{(d)}_{(f)} ≅ A_{(f)}` of homogeneous localizations, and these chart isomorphisms are
compatible with the transitions between charts.

## Main definitions

* `AlgebraicGeometry.Proj.veroneseIso`: the isomorphism `Proj A^{(d)} ≅ Proj A`.

## Main results

* `AlgebraicGeometry.Proj.iSup_basicOpen_veronese_eq_top`: the standard opens `D₊(f)` with
  `f ∈ 𝒜 (d k)`, `k > 0`, cover `Proj A`.
* `AlgebraicGeometry.Proj.awayι_veroneseIso_hom` and
  `AlgebraicGeometry.Proj.awayι_veroneseIso_inv`: on the standard chart of `f ∈ 𝒜 (d k)`,
  `k > 0`, the isomorphism and its inverse are `Spec` of the chart isomorphisms
  `A^{(d)}_{(f)} ≃ A_{(f)}`.
* `AlgebraicGeometry.Proj.veroneseIso_hom_preimage_basicOpen`: the isomorphism identifies the
  standard opens `D₊(f)` of `Proj A^{(d)}` and `Proj A`.
* `AlgebraicGeometry.Proj.map_veroneseMap_comp_veroneseIso_hom`: the isomorphism is natural in
  graded ring homomorphisms, through `Proj.map`.
* `AlgebraicGeometry.Proj.veroneseIso_hom_toSpecZero` and
  `AlgebraicGeometry.Proj.veroneseIso_hom_toSpecCoeff`: the isomorphism lies over
  `Spec A₀`, the degree-zero parts being identified, and over `Spec R`.

## References

* [The Stacks Project, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
* A. Grothendieck, *Éléments de géométrie algébrique II*, Publ. Math. IHÉS 8 (1961), §2.4.7.
-/

public section

open CategoryTheory Limits HomogeneousLocalization TauCeti.GradedAlgebra

namespace AlgebraicGeometry.Proj

universe u

section

variable {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ)

/-- The standard opens `D₊(f)` of `Proj A` with `f ∈ 𝒜 (d k)`, `k > 0`, cover `Proj A`: a point
outside `D₊(a)` for a homogeneous `a` of positive degree is outside `D₊(aᵈ)`. -/
theorem iSup_basicOpen_veronese_eq_top :
    ⨆ i : Σ k : ℕ+, veroneseGrading 𝒜 d k, basicOpen 𝒜 ((i.2 : veronese 𝒜 d) : A) = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  refine x.not_irrelevant_le
    ((HomogeneousIdeal.irrelevant_le 𝒜).mpr fun i hi a (ha : a ∈ 𝒜 i) ↦ ?_)
  have hd : a ^ d ∈ 𝒜 (d * i) := by simpa [mul_comm] using SetLike.pow_mem_graded d ha
  have := H ⟨⟨i, hi⟩, ⟨⟨a ^ d, mem_veronese_of_mem hd⟩, hd⟩⟩
  simp only [mem_basicOpen, not_not] at this
  exact x.isPrime.mem_of_pow_mem d this

variable [NeZero d]

/-- The affine open cover of `Proj A` by the standard charts `Spec A_{(f)}` with `f ∈ 𝒜 (d k)`,
`k > 0`. It is indexed like the standard affine open cover of `Proj A^{(d)}`
(`AlgebraicGeometry.Proj.affineOpenCover`). -/
private noncomputable def veroneseAffineOpenCover : (Proj 𝒜).AffineOpenCover where
  I₀ := Σ k : ℕ+, veroneseGrading 𝒜 d k
  X i := .of (Away 𝒜 ((i.2 : veronese 𝒜 d) : A))
  f i := awayι 𝒜 _ (mem_veroneseGrading.1 i.2.2) (Nat.mul_pos (NeZero.pos d) i.1.pos)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ x))).choose
  covers x := by
    -- the chart of the cover at `idx x` is `awayι 𝒜 f` by definition
    change x ∈ (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_basicOpen_veronese_eq_top 𝒜 d).ge (Set.mem_univ x))).choose_spec

/-- The morphism `Spec A^{(d)}_{(f)} ≅ Spec A_{(f)} ⟶ Proj A` on the chart of `f ∈ 𝒜 (d k)`,
`k > 0`. -/
private noncomputable def toProjChart {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    Spec (.of (Away (veroneseGrading 𝒜 d) f)) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (awayVeroneseEquiv f).symm.toRingHom) ≫
    awayι 𝒜 _ (mem_veroneseGrading.1 hf) (Nat.mul_pos (NeZero.pos d) hk)

/-- The morphism `Spec A_{(f)} ≅ Spec A^{(d)}_{(f)} ⟶ Proj A^{(d)}` on the chart of
`f ∈ 𝒜 (d k)`, `k > 0`. -/
private noncomputable def fromProjChart {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    Spec (.of (Away 𝒜 (f : A))) ⟶ Proj (veroneseGrading 𝒜 d) :=
  Spec.map (CommRingCat.ofHom (awayVeroneseEquiv f).toRingHom) ≫
    awayι (veroneseGrading 𝒜 d) f hf hk

private theorem SpecMap_awayMap_toProjChart {f g x : veronese 𝒜 d} {k k' : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) (hg : g ∈ veroneseGrading 𝒜 d k')
    (hx : x = f * g) :
    Spec.map (CommRingCat.ofHom (awayMap (veroneseGrading 𝒜 d) hg hx)) ≫
        toProjChart 𝒜 d hf hk =
      toProjChart 𝒜 d (hx ▸ SetLike.mul_mem_graded hf hg) (hk.trans_le (k.le_add_right k')) := by
  have : (awayVeroneseEquiv x).symm.toRingHom.comp
      (awayMap 𝒜 (mem_veroneseGrading.1 hg) (congrArg Subtype.val hx)) =
        (awayMap (veroneseGrading 𝒜 d) hg hx).comp (awayVeroneseEquiv f).symm.toRingHom :=
    RingHom.ext <| awayVeroneseEquiv_symm_awayMap _ _
  rw [toProjChart, toProjChart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← this,
    CommRingCat.ofHom_comp, Spec.map_comp_assoc, SpecMap_awayMap_awayι]
  -- the charts of `x` differ only in the form `d k + d k'` or `d (k + k')` of its degree
  congr 1

private theorem SpecMap_awayMap_fromProjChart {f g x : veronese 𝒜 d} {k k' : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) (hg : g ∈ veroneseGrading 𝒜 d k')
    (hx : x = f * g) :
    Spec.map (CommRingCat.ofHom
        (awayMap 𝒜 (mem_veroneseGrading.1 hg) (congrArg Subtype.val hx))) ≫
        fromProjChart 𝒜 d hf hk =
      fromProjChart 𝒜 d (hx ▸ SetLike.mul_mem_graded hf hg) (hk.trans_le (k.le_add_right k')) := by
  have : (awayVeroneseEquiv x).toRingHom.comp (awayMap (veroneseGrading 𝒜 d) hg hx) =
      (awayMap 𝒜 (mem_veroneseGrading.1 hg) (congrArg Subtype.val hx)).comp
        (awayVeroneseEquiv f).toRingHom :=
    RingHom.ext <| awayVeroneseEquiv_awayMap hg hx
  rw [fromProjChart, fromProjChart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← this,
    CommRingCat.ofHom_comp, Spec.map_comp_assoc, SpecMap_awayMap_awayι]

/-- The morphism `Proj A^{(d)} ⟶ Proj A`, glued from the chart morphisms `toProjChart`. -/
private noncomputable def veroneseToProj : Proj (veroneseGrading 𝒜 d) ⟶ Proj 𝒜 :=
  (affineOpenCover (veroneseGrading 𝒜 d)).openCover.glueMorphisms
    (fun i : Σ k : ℕ+, veroneseGrading 𝒜 d k ↦ toProjChart 𝒜 d i.2.2 i.1.pos)
    fun (i j : Σ k : ℕ+, veroneseGrading 𝒜 d k) ↦
      pullback_fst_awayι_comp_eq_snd_comp i.2.2 i.1.pos j.2.2 j.1.pos <|
        (SpecMap_awayMap_toProjChart 𝒜 d i.2.2 i.1.pos j.2.2 rfl).trans <|
          -- the two charts of `fg` differ only in the order of the degree `k + k'`
          .trans (by congr 1; exact add_comm _ _)
            (SpecMap_awayMap_toProjChart 𝒜 d j.2.2 j.1.pos i.2.2 (mul_comm _ _)).symm

/-- The morphism `Proj A ⟶ Proj A^{(d)}`, glued from the chart morphisms `fromProjChart`. -/
private noncomputable def projToVeronese : Proj 𝒜 ⟶ Proj (veroneseGrading 𝒜 d) :=
  (veroneseAffineOpenCover 𝒜 d).openCover.glueMorphisms
    (fun i : Σ k : ℕ+, veroneseGrading 𝒜 d k ↦ fromProjChart 𝒜 d i.2.2 i.1.pos)
    fun (i j : Σ k : ℕ+, veroneseGrading 𝒜 d k) ↦
      pullback_fst_awayι_comp_eq_snd_comp (mem_veroneseGrading.1 i.2.2)
        (Nat.mul_pos (NeZero.pos d) i.1.pos) (mem_veroneseGrading.1 j.2.2)
        (Nat.mul_pos (NeZero.pos d) j.1.pos) <|
        (SpecMap_awayMap_fromProjChart 𝒜 d i.2.2 i.1.pos j.2.2 rfl).trans <|
          -- the two charts of `fg` differ only in the order of the degree `k + k'`
          .trans (by congr 1; exact add_comm _ _)
            (SpecMap_awayMap_fromProjChart 𝒜 d j.2.2 j.1.pos i.2.2 (mul_comm _ _)).symm

@[reassoc]
private theorem awayι_veroneseToProj {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayι (veroneseGrading 𝒜 d) f hf hk ≫ veroneseToProj 𝒜 d = toProjChart 𝒜 d hf hk :=
  (affineOpenCover (veroneseGrading 𝒜 d)).openCover.ι_glueMorphisms _ _ ⟨⟨k, hk⟩, ⟨f, hf⟩⟩

@[reassoc]
private theorem awayι_projToVeronese {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayι 𝒜 (f : A) (mem_veroneseGrading.1 hf) (Nat.mul_pos (NeZero.pos d) hk) ≫
      projToVeronese 𝒜 d = fromProjChart 𝒜 d hf hk :=
  (veroneseAffineOpenCover 𝒜 d).openCover.ι_glueMorphisms _ _ ⟨⟨k, hk⟩, ⟨f, hf⟩⟩

private theorem awayι_veroneseToProj_projToVeronese {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayι (veroneseGrading 𝒜 d) f hf hk ≫ veroneseToProj 𝒜 d ≫ projToVeronese 𝒜 d =
      awayι (veroneseGrading 𝒜 d) f hf hk := by
  rw [awayι_veroneseToProj_assoc, toProjChart, Category.assoc, awayι_projToVeronese 𝒜 d hf hk,
    fromProjChart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    show (awayVeroneseEquiv f).symm.toRingHom.comp (awayVeroneseEquiv f).toRingHom = .id _ from
      RingHom.ext (awayVeroneseEquiv f).symm_apply_apply,
    CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

private theorem awayι_projToVeronese_veroneseToProj {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    awayι 𝒜 (f : A) (mem_veroneseGrading.1 hf) (Nat.mul_pos (NeZero.pos d) hk) ≫
      projToVeronese 𝒜 d ≫ veroneseToProj 𝒜 d =
      awayι 𝒜 (f : A) (mem_veroneseGrading.1 hf) (Nat.mul_pos (NeZero.pos d) hk) := by
  rw [awayι_projToVeronese_assoc 𝒜 d hf hk, fromProjChart, Category.assoc,
    awayι_veroneseToProj 𝒜 d hf hk,
    toProjChart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    show (awayVeroneseEquiv f).toRingHom.comp (awayVeroneseEquiv f).symm.toRingHom = .id _ from
      RingHom.ext (awayVeroneseEquiv f).apply_symm_apply,
    CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- **The projective spectrum of a Veronese subalgebra.** For `d ≠ 0`, the projective spectra of
`A^{(d)} = ⨁ₖ 𝒜 (d k)` and of `A` are isomorphic. On the chart of `f ∈ 𝒜 (d k)`, `k > 0`, it is
`Spec` of the isomorphism `A^{(d)}_{(f)} ≃ A_{(f)}`
(`AlgebraicGeometry.Proj.awayι_veroneseIso_hom`). -/
noncomputable def veroneseIso : Proj (veroneseGrading 𝒜 d) ≅ Proj 𝒜 where
  hom := veroneseToProj 𝒜 d
  inv := projToVeronese 𝒜 d
  hom_inv_id := (affineOpenCover (veroneseGrading 𝒜 d)).openCover.hom_ext _ _ fun i ↦
    (awayι_veroneseToProj_projToVeronese 𝒜 d i.2.2 i.1.pos).trans (Category.comp_id _).symm
  inv_hom_id := (veroneseAffineOpenCover 𝒜 d).openCover.hom_ext _ _ fun i ↦
    (awayι_projToVeronese_veroneseToProj 𝒜 d i.2.2 i.1.pos).trans (Category.comp_id _).symm

/-- On the standard chart of `f ∈ 𝒜 (d k)`, `k > 0`, the isomorphism
`Proj A^{(d)} ≅ Proj A` is `Spec` of the chart isomorphism `A^{(d)}_{(f)} ≃ A_{(f)}`. -/
@[reassoc]
theorem awayι_veroneseIso_hom {f : veronese 𝒜 d} {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k)
    (hk : 0 < k) :
    awayι (veroneseGrading 𝒜 d) f hf hk ≫ (veroneseIso 𝒜 d).hom =
      Spec.map (CommRingCat.ofHom (awayVeroneseEquiv f).symm.toRingHom) ≫
        awayι 𝒜 (f : A) (mem_veroneseGrading.1 hf) (Nat.mul_pos (NeZero.pos d) hk) :=
  awayι_veroneseToProj 𝒜 d hf hk

/-- On the standard chart of `f ∈ 𝒜 (d k)`, `k > 0`, the isomorphism
`Proj A ≅ Proj A^{(d)}` is `Spec` of the inverse chart isomorphism `A_{(f)} ≃ A^{(d)}_{(f)}`. -/
@[reassoc]
theorem awayι_veroneseIso_inv {f : veronese 𝒜 d} {k : ℕ} (hf : f ∈ veroneseGrading 𝒜 d k)
    (hk : 0 < k) :
    awayι 𝒜 (f : A) (mem_veroneseGrading.1 hf) (Nat.mul_pos (NeZero.pos d) hk) ≫
        (veroneseIso 𝒜 d).inv =
      Spec.map (CommRingCat.ofHom (awayVeroneseEquiv f).toRingHom) ≫
        awayι (veroneseGrading 𝒜 d) f hf hk :=
  awayι_projToVeronese 𝒜 d hf hk

/-- The isomorphism `Proj A^{(d)} ≅ Proj A` identifies the standard opens `D₊(f)` for
`f ∈ 𝒜 (d k)`, `k > 0`. -/
theorem veroneseIso_hom_preimage_basicOpen {f : veronese 𝒜 d} {k : ℕ}
    (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
    (veroneseIso 𝒜 d).hom ⁻¹ᵁ basicOpen 𝒜 (f : A) = basicOpen (veroneseGrading 𝒜 d) f := by
  rw [← Scheme.Hom.inv_image, ← opensRange_awayι 𝒜 _ (mem_veroneseGrading.1 hf)
      (Nat.mul_pos (NeZero.pos d) hk), ← Scheme.Hom.opensRange_comp]
  have : IsIso (CommRingCat.ofHom (awayVeroneseEquiv f).toRingHom) :=
    (awayVeroneseEquiv f).toRingEquiv.toCommRingCatIso.isIso_hom
  -- `opensRange` takes an `IsOpenImmersion` instance, so the chart formula is rewritten by `congr`
  trans (Spec.map (CommRingCat.ofHom (awayVeroneseEquiv f).toRingHom) ≫
    awayι (veroneseGrading 𝒜 d) f hf hk).opensRange
  · congr 1
    exact awayι_veroneseIso_inv 𝒜 d hf hk
  · rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_awayι]

section Map

variable {R' : Type*} {B : Type u} [CommRing R'] [CommRing B] [Algebra R' B]
  {ℬ : ℕ → Submodule R' B} [GradedAlgebra ℬ]

/-- The isomorphism `Proj A^{(d)} ≅ Proj A` is natural in graded ring homomorphisms `f : A → B`
inducing morphisms `Proj B ⟶ Proj A`. -/
@[reassoc]
theorem map_veroneseMap_comp_veroneseIso_hom (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    map (veroneseMap d f) (irrelevant_le_map_veroneseMap d f hf) ≫ (veroneseIso 𝒜 d).hom =
      (veroneseIso ℬ d).hom ≫ map f hf := by
  have (s : veronese 𝒜 d) (k : ℕ) (hs : s ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
      awayι _ (veroneseMap d f s) ((veroneseMap d f).map_mem hs) hk ≫
          map (veroneseMap d f) (irrelevant_le_map_veroneseMap d f hf) ≫ (veroneseIso 𝒜 d).hom =
        awayι _ (veroneseMap d f s) ((veroneseMap d f).map_mem hs) hk ≫
          (veroneseIso ℬ d).hom ≫ map f hf := by
    have hpos := Nat.mul_pos (NeZero.pos d) hk
    have hring : CommRingCat.ofHom (awayVeroneseEquiv s).symm.toRingHom ≫
        CommRingCat.ofHom (Away.map (veroneseMap d f) s) =
          CommRingCat.ofHom (Away.map f (s : A)) ≫
            CommRingCat.ofHom (awayVeroneseEquiv (veroneseMap d f s)).symm.toRingHom :=
      CommRingCat.hom_ext <| RingHom.ext fun a ↦ (awayVeroneseEquiv_symm_map_veroneseMap f a).symm
    rw [awayι_comp_map_assoc _ _ hk _ hs, awayι_veroneseIso_hom, awayι_veroneseIso_hom_assoc,
      ← Spec.map_comp_assoc, hring, Spec.map_comp_assoc]
    -- `veroneseMap d f s` is `f s` in `B`, so the chart square of `Proj.map f` applies
    exact congrArg (_ ≫ ·) (awayι_comp_map f hf hpos _ (mem_veroneseGrading.1 hs)).symm
  exact (mapAffineOpenCover _ (irrelevant_le_map_veroneseMap d f hf)).openCover.hom_ext _ _
    fun i ↦ this _ _ i.2.2 i.1.pos

end Map

/-- The isomorphism `Proj A^{(d)} ≅ Proj A` lies over the identification `A^{(d)}_0 ≃ A_0` of
the degree-zero parts. -/
@[reassoc]
theorem veroneseIso_hom_toSpecZero :
    (veroneseIso 𝒜 d).hom ≫ toSpecZero 𝒜 = toSpecZero (veroneseGrading 𝒜 d) ≫
      Spec.map (CommRingCat.ofHom (veroneseGradingZeroEquiv 𝒜 d).symm.toRingHom) := by
  have (f : veronese 𝒜 d) (k : ℕ) (hf : f ∈ veroneseGrading 𝒜 d k) (hk : 0 < k) :
      awayι _ f hf hk ≫ (veroneseIso 𝒜 d).hom ≫ toSpecZero 𝒜 = awayι _ f hf hk ≫
        toSpecZero (veroneseGrading 𝒜 d) ≫
          Spec.map (CommRingCat.ofHom (veroneseGradingZeroEquiv 𝒜 d).symm.toRingHom) := by
    rw [awayι_veroneseIso_hom_assoc, awayι_toSpecZero, awayι_toSpecZero_assoc, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext awayVeroneseEquiv_symm_fromZeroRingHom
  exact (affineOpenCover (veroneseGrading 𝒜 d)).openCover.hom_ext _ _ fun i ↦
    this _ _ i.2.2 i.1.pos

end

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ) [NeZero d]

/-- The isomorphism `Proj A^{(d)} ≅ Proj A` lies over the coefficient ring: it commutes with the
structure morphisms to `Spec R`. -/
@[reassoc (attr := simp)]
theorem veroneseIso_hom_toSpecCoeff :
    (veroneseIso 𝒜 d).hom ≫ toSpecCoeff 𝒜 = toSpecCoeff (veroneseGrading 𝒜 d) := by
  rw [toSpecCoeff_def, veroneseIso_hom_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    toSpecCoeff_def]
  congr 3
  ext r
  simp

/-- The inverse isomorphism `Proj A ≅ Proj A^{(d)}` lies over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem veroneseIso_inv_toSpecCoeff :
    (veroneseIso 𝒜 d).inv ≫ toSpecCoeff (veroneseGrading 𝒜 d) = toSpecCoeff 𝒜 := by
  rw [Iso.inv_comp_eq, veroneseIso_hom_toSpecCoeff]

end AlgebraicGeometry.Proj
