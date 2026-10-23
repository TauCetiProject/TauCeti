/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic
public import TauCeti.Topology.Homotopy.CollaredTrack

/-!
# Topological concordance of locally flat embeddings

Two embeddings `f g : N → M` are *concordant* when they are the two ends of an embedding of
`N × [0, 1]` into `M × [0, 1]`; for knots, `N` is the circle and the track of the concordance is an
annulus in `M × [0, 1]`. In the topological category the track has to be *locally flat*
(`TauCeti.IsLocallyFlat`): an arbitrary topological embedding of the annulus can be wild, and a
concordance relation allowing wild tracks would not be the one the knot concordance group is built
on. Topological concordance is therefore defined here as the collared-track relation of
`TauCeti.IsCollaredTrack` with a locally flat track: a `TopologicalConcordance F F' f g` is a
locally flat embedding `N × ℝ → M × ℝ`, with tangential model `F × ℝ` and complementary model `F'`,
which is `f × id` on a collar of the initial end and `g × id` on a collar of the final end. Its
restriction to `N × [0, 1]` is an ordinary locally flat concordance which is a product near both
ends, and the uniform collars are what make two concordances stack.

The relation is kept apart from smooth concordance (`TauCeti.SmoothEmbedding.Concordance`), whose
track is a smooth embedding: the gap between the two is genuine, since a topologically slice knot
need not be smoothly slice. Smooth concordances are topological concordances; that comparison lives
in `TauCeti.Geometry.Manifold.LocallyFlat.Concordance.Smooth`.

Local flatness of the track does not follow for its two ends, since a flattening chart of `M × ℝ`
along the track does not restrict to a chart of `M`, so the relation is stated on arbitrary maps and
is an equivalence relation on the locally flat embeddings: the constant concordance at `f` needs `f`
to be locally flat, while reversing and stacking do not.

## Main definitions

* `TauCeti.TopologicalConcordance F F' f g`: a topological concordance from `f` to `g`, in collared
  form, with tangential model `F × ℝ` and complementary model `F'`.
* `TauCeti.TopologicalConcordance.refl`, `symm`, `trans`: the constant concordance at a locally flat
  embedding, the reversed concordance and the stacked concordance.
* `TauCeti.TopologicalConcordance.transHomeomorph`, `compHomeomorph`: transport along a
  homeomorphism of the ambient space or of the source.
* `TauCeti.TopologicalConcordance.ofAmbientIsotopy`: the trace of an ambient isotopy along a locally
  flat embedding.
* `TauCeti.TopologicallyConcordant F F' f g`: the topological concordance relation.

## Main results

* `TauCeti.TopologicallyConcordant.equivalence`: topological concordance is an equivalence relation
  on the locally flat embeddings, with no finite-dimensionality assumption, since local flatness is
  a local property and the stacked track is glued along an open cover.
* `TauCeti.AmbientIsotopic.topologicallyConcordant`: ambient isotopic maps are topologically
  concordant as soon as the first is locally flat.

## References

* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448, for
  concordance of embeddings.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for smooth versus topological knot concordance.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

variable {M N N' P F F' : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
  [TopologicalSpace P] [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

/-- Conjugating a locally flat track by an affine change of time keeps it locally flat. -/
theorem IsLocallyFlat.conjTime {Φ : N × ℝ → M × ℝ} (h : IsLocallyFlat (F × ℝ) F' Φ) {a : ℝ}
    (b : ℝ) (ha : a ≠ 0) : IsLocallyFlat (F × ℝ) F' (conjTime Φ a b) := by
  rw [conjTime_eq_comp Φ b ha]
  exact (h.comp_homeomorph _).homeomorph_comp _

variable (F F') in
/-- A **topological concordance** from `f` to `g`, in collared form: a locally flat embedding of
`N × ℝ` into `M × ℝ`, with tangential model `F × ℝ` and complementary model `F'`, which is `f × id`
on a collar of the initial end and `g × id` on a collar of the final end, and maps the open slab
`N × (0, 1)` into `M × (0, 1)`. -/
structure TopologicalConcordance (f g : N → M) where
  /-- The track of the concordance. -/
  toFun : N × ℝ → M × ℝ
  /-- The track is a locally flat embedding, with tangential model `F × ℝ` and complementary model
  `F'`. -/
  isLocallyFlat_toFun : IsLocallyFlat (F × ℝ) F' toFun
  /-- The track is `f × id` near the initial end and `g × id` near the final end, and maps the open
  slab `N × (0, 1)` into `M × (0, 1)`. -/
  isCollaredTrack_toFun : IsCollaredTrack f g toFun

variable (F F') in
/-- Two maps are **topologically concordant**, for the tangential model `F` and the complementary
model `F'`, when there is a topological concordance from one to the other. -/
def TopologicallyConcordant (f g : N → M) : Prop :=
  Nonempty (TopologicalConcordance F F' f g)

/-- Two maps are topologically concordant exactly when their concordance type is nonempty. -/
theorem topologicallyConcordant_iff_nonempty {f g : N → M} :
    TopologicallyConcordant F F' f g ↔ Nonempty (TopologicalConcordance F F' f g) :=
  Iff.rfl

namespace TopologicalConcordance

variable {f g h : N → M}

instance instFunLike : FunLike (TopologicalConcordance F F' f g) (N × ℝ) (M × ℝ) where
  coe Φ := Φ.toFun
  coe_injective Φ Ψ hΦΨ := by
    cases Φ
    cases Ψ
    congr

@[simp]
theorem coe_mk (Φ : N × ℝ → M × ℝ) (hΦ : IsLocallyFlat (F × ℝ) F' Φ)
    (hΦ' : IsCollaredTrack f g Φ) : ⇑(mk Φ hΦ hΦ' : TopologicalConcordance F F' f g) = Φ :=
  (rfl)

/-- Two topological concordances with the same track are equal. -/
@[ext]
theorem ext {Φ Ψ : TopologicalConcordance F F' f g} (hΦΨ : ∀ p, Φ p = Ψ p) : Φ = Ψ :=
  DFunLike.coe_injective (funext hΦΨ)

variable (Φ : TopologicalConcordance F F' f g)

/-- The track of a topological concordance is locally flat. -/
theorem isLocallyFlat : IsLocallyFlat (F × ℝ) F' Φ :=
  Φ.isLocallyFlat_toFun

/-- The track of a topological concordance is a collared track from `f` to `g`. -/
theorem isCollaredTrack : IsCollaredTrack f g Φ :=
  Φ.isCollaredTrack_toFun

/-- The track of a topological concordance is a topological embedding. -/
theorem isEmbedding : IsEmbedding Φ :=
  Φ.isLocallyFlat.isEmbedding

/-- The track of a topological concordance is continuous. -/
theorem continuous : Continuous Φ :=
  Φ.isEmbedding.continuous

/-- At time `0` a topological concordance is its initial map. -/
@[simp]
theorem apply_zero (x : N) : Φ (x, 0) = (f x, 0) :=
  Φ.isCollaredTrack.apply_zero x

/-- At time `1` a topological concordance is its final map. -/
@[simp]
theorem apply_one (x : N) : Φ (x, 1) = (g x, 1) :=
  Φ.isCollaredTrack.apply_one x

/-! ### Homeomorphisms -/

/-- A homeomorphism of the ambient space carries a topological concordance from `f` to `g` to one
from `e ∘ f` to `e ∘ g`. -/
def transHomeomorph (e : M ≃ₜ P) : TopologicalConcordance F F' (e ∘ f) (e ∘ g) where
  toFun := Prod.map e id ∘ Φ
  isLocallyFlat_toFun := by
    have he : ⇑(e.prodCongr (Homeomorph.refl ℝ)) = Prod.map e id := by
      funext p
      simp
    exact he ▸ Φ.isLocallyFlat.homeomorph_comp (e.prodCongr (Homeomorph.refl ℝ))
  isCollaredTrack_toFun := Φ.isCollaredTrack.prodMap_id_comp e

@[simp]
theorem transHomeomorph_apply (e : M ≃ₜ P) (p : N × ℝ) :
    Φ.transHomeomorph e p = (e (Φ p).1, (Φ p).2) := by
  simp [transHomeomorph, Prod.map]

/-- A homeomorphism of the source reparametrizes a topological concordance from `f` to `g` into
one from `f ∘ e` to `g ∘ e`. -/
def compHomeomorph (e : N' ≃ₜ N) : TopologicalConcordance F F' (f ∘ e) (g ∘ e) where
  toFun := Φ ∘ Prod.map e id
  isLocallyFlat_toFun := by
    have he : ⇑(e.prodCongr (Homeomorph.refl ℝ)) = Prod.map e id := by
      funext p
      simp
    exact he ▸ Φ.isLocallyFlat.comp_homeomorph (e.prodCongr (Homeomorph.refl ℝ))
  isCollaredTrack_toFun := Φ.isCollaredTrack.comp_prodMap_id e

@[simp]
theorem compHomeomorph_apply (e : N' ≃ₜ N) (p : N' × ℝ) :
    Φ.compHomeomorph e p = Φ (e p.1, p.2) := by
  simp [compHomeomorph, Prod.map]

/-! ### The constant, the reversed and the stacked concordance -/

/-- The constant topological concordance from a locally flat embedding `f` to itself, with track
`f × id`. -/
def refl {f : N → M} (hf : IsLocallyFlat F F' f) : TopologicalConcordance F F' f f where
  toFun := Prod.map f id
  isLocallyFlat_toFun := hf.prodMap_of_isOpenEmbedding IsOpenEmbedding.id
  isCollaredTrack_toFun := isCollaredTrack_prodMap_id f

@[simp]
theorem refl_apply {f : N → M} (hf : IsLocallyFlat F F' f) (p : N × ℝ) :
    refl hf p = (f p.1, p.2) := by
  simp [refl, Prod.map]

/-- The reversed topological concordance from `g` to `f`, obtained by reflecting time in
`1 / 2`. -/
def symm : TopologicalConcordance F F' g f where
  toFun := reverseTime Φ
  isLocallyFlat_toFun := by
    rw [reverseTime_def]
    exact Φ.isLocallyFlat.conjTime 1 (by norm_num)
  isCollaredTrack_toFun := Φ.isCollaredTrack.reverseTime

@[simp]
theorem symm_apply (x : N) (t : ℝ) :
    Φ.symm (x, t) = ((Φ (x, 1 - t)).1, 1 - (Φ (x, 1 - t)).2) := by
  simp [symm]

/-- Reversing a topological concordance twice gives it back. -/
@[simp]
theorem symm_symm : Φ.symm.symm = Φ := by
  ext ⟨x, t⟩ <;> simp

/-- The stacked topological concordance from `f` to `h`: the concordance `Φ` from `f` to `g` at
triple speed during `[0, 1/3]`, then the constant concordance at `g`, then the concordance `Ψ` from
`g` to `h` at triple speed during `[2/3, 1]`. The track is glued from two open slabs, on each of
which it is a rescaling of one of the two tracks, and local flatness is a local property. -/
def trans (Ψ : TopologicalConcordance F F' g h) : TopologicalConcordance F F' f h where
  toFun := stack Φ Ψ
  isLocallyFlat_toFun := by
    have hΦ := Φ.isCollaredTrack
    have hΨ := Ψ.isCollaredTrack
    have hlow : IsOpen {q : N × ℝ | q.2 < 2 / 3} := isOpen_lt continuous_snd continuous_const
    have hup : IsOpen {q : N × ℝ | 1 / 3 < q.2} := isOpen_lt continuous_const continuous_snd
    refine IsLocallyFlat.of_forall_exists_isOpen
      (hΦ.isEmbedding_stack hΨ Φ.isEmbedding Ψ.isEmbedding) fun p => ?_
    rcases lt_or_ge p.2 (2 / 3) with hp | hp
    · refine ⟨_, hlow, hp, ?_⟩
      have heq : stack ⇑Φ ⇑Ψ ∘ (Subtype.val : {q : N × ℝ | q.2 < 2 / 3} → N × ℝ) =
          conjTime ⇑Φ 3 0 ∘ Subtype.val :=
        funext fun q => hΦ.stack_eqOn_lower hΨ q.2
      rw [heq]
      exact (Φ.isLocallyFlat.conjTime 0 (by norm_num)).restrict hlow
    · refine ⟨_, hup, lt_of_lt_of_le (by norm_num) hp, ?_⟩
      have heq : stack ⇑Φ ⇑Ψ ∘ (Subtype.val : {q : N × ℝ | 1 / 3 < q.2} → N × ℝ) =
          conjTime ⇑Ψ 3 (-2) ∘ Subtype.val :=
        funext fun q => hΦ.stack_eqOn_upper hΨ q.2
      rw [heq]
      exact (Ψ.isLocallyFlat.conjTime (-2) (by norm_num)).restrict hup
  isCollaredTrack_toFun := Φ.isCollaredTrack.stack Ψ.isCollaredTrack

/-- Before time `1 / 2` the stacked concordance runs the first concordance at triple speed. -/
theorem trans_apply_of_le (Ψ : TopologicalConcordance F F' g h) (x : N) {t : ℝ}
    (ht : t ≤ 1 / 2) : Φ.trans Ψ (x, t) = ((Φ (x, 3 * t)).1, (Φ (x, 3 * t)).2 / 3) := by
  simp only [trans, coe_mk, stack_apply_of_le _ _ x ht]

/-- After time `1 / 2` the stacked concordance runs the second concordance at triple speed. -/
theorem trans_apply_of_lt (Ψ : TopologicalConcordance F F' g h) (x : N) {t : ℝ}
    (ht : 1 / 2 < t) :
    Φ.trans Ψ (x, t) = ((Ψ (x, 3 * t - 2)).1, ((Ψ (x, 3 * t - 2)).2 + 2) / 3) := by
  simp only [trans, coe_mk, stack_apply_of_lt _ _ x ht]

/-! ### Ambient isotopies -/

/-- The clamp `t ↦ 2 * t - 1 / 2` cut down to the unit interval: it is `0` for `t ≤ 1 / 4` and `1`
for `t ≥ 3 / 4`, so reparametrising an ambient isotopy by it makes the isotopy constant on collars
of both ends. -/
def collarClamp : C(ℝ, I) :=
  ⟨fun t => projIcc 0 1 zero_le_one (2 * t - 1 / 2), continuous_projIcc.comp (by fun_prop)⟩

@[simp]
theorem collarClamp_apply (t : ℝ) : collarClamp t = projIcc 0 1 zero_le_one (2 * t - 1 / 2) :=
  (rfl)

theorem collarClamp_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : collarClamp t = 0 := by
  rw [collarClamp_apply, projIcc_of_le_left _ (by linarith)]
  rfl

theorem collarClamp_eq_one_of_le {t : ℝ} (ht : 3 / 4 ≤ t) : collarClamp t = 1 := by
  rw [collarClamp_apply, projIcc_of_right_le _ (by linarith)]
  rfl

/-- **The trace of an ambient isotopy** `Φ` of `M` along a locally flat embedding `f`: the
topological concordance `(x, t) ↦ (Φ (ρ t, f x), t)` from `f` to `Φ.final ∘ f`, where `ρ` is the
clamp `TauCeti.collarClamp`. -/
def ofAmbientIsotopy (Φ : AmbientIsotopy M) {f : N → M} (hf : IsLocallyFlat F F' f) :
    TopologicalConcordance F F' f (Φ.final ∘ f) where
  toFun := Φ.reparamHomeomorph collarClamp ∘ Prod.map f id
  isLocallyFlat_toFun := (hf.prodMap_of_isOpenEmbedding IsOpenEmbedding.id).homeomorph_comp _
  isCollaredTrack_toFun :=
    { exists_pos_apply_eq_left := ⟨1 / 4, by norm_num, fun x t ht => by
        simp [collarClamp_eq_zero_of_le ht]⟩
      exists_pos_apply_eq_right := ⟨1 / 4, by norm_num, fun x t ht => by
        have ht' : 3 / 4 ≤ t := by linarith
        simp [collarClamp_eq_one_of_le ht']⟩
      snd_apply_mem_Ioo := fun x t ht => by simpa using ht }

@[simp]
theorem ofAmbientIsotopy_apply (Φ : AmbientIsotopy M) {f : N → M} (hf : IsLocallyFlat F F' f)
    (p : N × ℝ) :
    ofAmbientIsotopy Φ hf p = (Φ.toContinuousMap (collarClamp p.2, f p.1), p.2) := by
  simp [ofAmbientIsotopy, Prod.map]

end TopologicalConcordance

/-! ### The topological concordance relation -/

namespace TopologicallyConcordant

variable {f g h : N → M}

/-- A topological concordance witnesses topological concordance. -/
theorem of_topologicalConcordance (Φ : TopologicalConcordance F F' f g) :
    TopologicallyConcordant F F' f g :=
  topologicallyConcordant_iff_nonempty.2 ⟨Φ⟩

/-- A homeomorphism of the ambient space preserves topological concordance. -/
theorem transHomeomorph (hfg : TopologicallyConcordant F F' f g) (e : M ≃ₜ P) :
    TopologicallyConcordant F F' (e ∘ f) (e ∘ g) :=
  Nonempty.map (fun Φ => Φ.transHomeomorph e) (topologicallyConcordant_iff_nonempty.1 hfg)

/-- Reparametrizing the source by a homeomorphism preserves topological concordance. -/
theorem compHomeomorph (hfg : TopologicallyConcordant F F' f g) (e : N' ≃ₜ N) :
    TopologicallyConcordant F F' (f ∘ e) (g ∘ e) :=
  Nonempty.map (fun Φ => Φ.compHomeomorph e) (topologicallyConcordant_iff_nonempty.1 hfg)

/-- A locally flat embedding is topologically concordant to itself. -/
theorem refl {f : N → M} (hf : IsLocallyFlat F F' f) : TopologicallyConcordant F F' f f :=
  topologicallyConcordant_iff_nonempty.2 ⟨.refl hf⟩

/-- Topological concordance is symmetric. -/
@[symm]
theorem symm (hfg : TopologicallyConcordant F F' f g) : TopologicallyConcordant F F' g f :=
  Nonempty.map TopologicalConcordance.symm (topologicallyConcordant_iff_nonempty.1 hfg)

/-- Topological concordance is transitive. -/
@[trans]
theorem trans (hfg : TopologicallyConcordant F F' f g) (hgh : TopologicallyConcordant F F' g h) :
    TopologicallyConcordant F F' f h :=
  Nonempty.elim (topologicallyConcordant_iff_nonempty.1 hfg) fun Φ =>
    Nonempty.map (fun Ψ => Φ.trans Ψ) (topologicallyConcordant_iff_nonempty.1 hgh)

/-- **Topological concordance is an equivalence relation on locally flat embeddings.** -/
theorem equivalence :
    Equivalence fun f g : {f : N → M // IsLocallyFlat F F' f} =>
      TopologicallyConcordant F F' f.1 g.1 :=
  ⟨fun f => refl f.2, symm, trans⟩

variable (F F') in
/-- Topological concordance of locally flat embeddings, packaged as a setoid. -/
def setoid (N M : Type*) [TopologicalSpace N] [TopologicalSpace M] :
    Setoid {f : N → M // IsLocallyFlat F F' f} where
  r f g := TopologicallyConcordant F F' f.1 g.1
  iseqv := equivalence

/-- The relation of the topological concordance setoid is topological concordance. -/
@[simp]
theorem setoid_r_iff {f g : {f : N → M // IsLocallyFlat F F' f}} :
    (setoid F F' N M).r f g ↔ TopologicallyConcordant F F' f.1 g.1 :=
  Iff.rfl

end TopologicallyConcordant

/-- **Ambient isotopic maps are topologically concordant**, as soon as the first is locally flat,
through the trace of the ambient isotopy. -/
theorem AmbientIsotopic.topologicallyConcordant {f g : C(N, M)} (hfg : AmbientIsotopic f g)
    (hf : IsLocallyFlat F F' f) : TopologicallyConcordant F F' f g := by
  obtain ⟨Φ, hΦ⟩ := ambientIsotopic_def.1 hfg
  have hg : Φ.final ∘ f = g := by rw [← ContinuousMap.coe_comp, hΦ]
  exact topologicallyConcordant_iff_nonempty.2 ⟨hg ▸ TopologicalConcordance.ofAmbientIsotopy Φ hf⟩

end TauCeti
