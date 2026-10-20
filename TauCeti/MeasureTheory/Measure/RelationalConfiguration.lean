/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Projective
import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable

/-!
# Finite measures on relational configurations

A relational configuration is a Boolean value for every atom, and configurations carry the product
σ-algebra. A finite measure on configurations is therefore determined by its finite-dimensional
laws, the laws of the values at finite sets of atoms. Over the vertex set `ℕ`, every finite set of
atoms involves finitely many vertices, so a finite measure is already determined by its windows,
the restrictions along `Fin.val : Fin n → ℕ`.

## Main results

* `TauCeti.RelationalConfiguration.measure_ext_of_forall_finset` — a finite measure on
  configurations is determined by the laws of its values at finite sets of atoms;
* `TauCeti.RelationalConfiguration.map_restrict_eq_of_forall_finset` — the restriction of a
  finite measure along a vertex map is determined by the laws of the finite sets of atoms that are
  relabelled from the source;
* `TauCeti.RelationalConfiguration.measure_ext_of_map_restrict_val` — a finite measure on
  configurations over `ℕ` is determined by its windows;
* `TauCeti.RelationalConfiguration.exists_map_restrict_val_eq` — conversely, probability laws on
  the windows that are consistent under the inclusions `Fin n → Fin (n + 1)` are the windows of a
  probability law over `ℕ`.

The extension theorem is Kolmogorov's: the window laws prescribe the law of the values at every
finite set of atoms, these laws form a projective family over the countably many atoms, and
`TauCeti.Measure.exists_isProjectiveLimit_of_countable` realizes it. The construction follows the
graph case `TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Basic`, which
follows C. Freer, `cameronfreer/graphon` at commit `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`,
Apache-2.0, `Graphon/InfiniteLaw.lean`, with the Boolean edge coordinates of a graph replaced by
the Boolean atom coordinates of a configuration.
-/

public section

open MeasureTheory

open _root_.FirstOrder (Language)

namespace TauCeti

namespace RelationalConfiguration

variable {L : Language} {V W : Type*}

/-- Reading off a finite set of atoms is measurable. -/
@[fun_prop]
theorem measurable_restrict_eval (J : Finset (Atom L V)) :
    Measurable fun c : RelationalConfiguration L V => J.restrict c.eval := by
  fun_prop

/-- **A finite measure on configurations is determined by its finite-dimensional laws**, the laws
of the values at finite sets of atoms. -/
theorem measure_ext_of_forall_finset {μ ν : Measure (RelationalConfiguration L V)}
    [IsFiniteMeasure μ]
    (h : ∀ J : Finset (Atom L V),
      μ.map (fun c => J.restrict c.eval) = ν.map (fun c => J.restrict c.eval)) : μ = ν := by
  have heval : Measurable fun c : RelationalConfiguration L V => c.eval :=
    measurable_pi_iff.2 measurable_eval
  -- The laws of the atom values are projective limits of the same family.
  have hcoord : μ.map (fun c => c.eval) = ν.map (fun c => c.eval) :=
    IsProjectiveLimit.unique (P := fun J => μ.map fun c => J.restrict c.eval)
      (fun J => by rw [Measure.map_map (Finset.measurable_restrict J) heval]; rfl)
      fun J => by rw [Measure.map_map (Finset.measurable_restrict J) heval]; exact (h J).symm
  have hmk : ∀ ρ : Measure (RelationalConfiguration L V), (ρ.map fun c => c.eval).map mk = ρ :=
    fun ρ => by
      have hid : (mk ∘ fun c : RelationalConfiguration L V => c.eval) = id :=
        funext fun c => ext fun a => eval_mk _ a
      rw [Measure.map_map measurable_mk heval, hid, Measure.map_id]
  rw [← hmk μ, hcoord, hmk]

/-- Two finite measures on configurations have the same restriction along a vertex map `f` as soon
as they give the same law to every finite set of atoms relabelled along `f`. -/
theorem map_restrict_eq_of_forall_finset {μ ν : Measure (RelationalConfiguration L W)}
    [IsFiniteMeasure μ] (f : V → W)
    (h : ∀ J : Finset (Atom L W), (∀ a ∈ J, ∃ b : Atom L V, b.map f = a) →
      μ.map (fun c => J.restrict c.eval) = ν.map (fun c => J.restrict c.eval)) :
    μ.map (restrict f) = ν.map (restrict f) := by
  classical
  refine measure_ext_of_forall_finset fun J => ?_
  -- Reading the atoms of `J` after restricting along `f` reads the atoms of `J.image (map f)`.
  have hread : (fun c : RelationalConfiguration L W => J.restrict (c.restrict f).eval) =
      (fun x j => x ⟨j.1.map f, Finset.mem_image_of_mem _ j.2⟩) ∘
        fun c => (J.image (Atom.map f)).restrict c.eval := by
    funext c
    ext j
    simp
  have hlaw : ∀ ρ : Measure (RelationalConfiguration L W),
      (ρ.map (restrict f)).map (fun d => J.restrict d.eval) =
        (ρ.map fun c => (J.image (Atom.map f)).restrict c.eval).map
          fun x j => x ⟨j.1.map f, Finset.mem_image_of_mem _ j.2⟩ := fun ρ => by
    rw [Measure.map_map (measurable_restrict_eval J) (measurable_restrict f),
      Measure.map_map (measurable_of_countable _) (measurable_restrict_eval _)]
    exact congrArg ρ.map hread
  refine (hlaw μ).trans ((congrArg (Measure.map _) (h _ fun a ha => ?_)).trans (hlaw ν).symm)
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 ha
  exact ⟨b, hb⟩

/-- **A finite measure on configurations over `ℕ` is determined by its windows**, the
restrictions along `Fin.val : Fin n → ℕ`: every finite set of atoms lies in some window, where
the configuration is recovered by extending its restriction. -/
theorem measure_ext_of_map_restrict_val {μ ν : Measure (RelationalConfiguration L ℕ)}
    [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (restrict (Fin.val : Fin n → ℕ)) = ν.map (restrict Fin.val)) : μ = ν := by
  refine measure_ext_of_forall_finset fun J => ?_
  obtain ⟨n, hn⟩ := Atom.exists_forall_map_val J
  -- The atoms of `J` are read off the extension of the window below `n`.
  have hread : (fun c : RelationalConfiguration L ℕ => J.restrict c.eval) =
      (fun d => J.restrict (d.extend Fin.val).eval) ∘ restrict (Fin.val : Fin n → ℕ) := by
    funext c
    ext a
    obtain ⟨b, hb⟩ := hn a a.2
    simp [← hb, Fin.val_injective]
  have hm : Measurable fun d : RelationalConfiguration L (Fin n) =>
      J.restrict (d.extend Fin.val).eval :=
    (measurable_restrict_eval J).comp (measurable_extend _)
  rw [hread, ← Measure.map_map hm (measurable_restrict _), h, Measure.map_map hm
    (measurable_restrict _)]

/-! ### Extension of window laws to `ℕ` -/

section Extension

variable (P : ∀ n, Measure (RelationalConfiguration L (Fin n)))

/-- Window laws consistent under the successive inclusions `Fin.castSucc` are consistent under
every inclusion `Fin.castLE`. -/
private theorem map_restrict_castLE_of_map_restrict_castSucc
    (hP : ∀ n, (P (n + 1)).map (restrict Fin.castSucc) = P n) {m n : ℕ} (hmn : m ≤ n) :
    (P n).map (restrict (Fin.castLE hmn)) = P m := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have hid : (Fin.castLE (le_refl m) : Fin m → Fin m) = id := funext (Fin.castLE_refl _)
    rw [hid]
    exact (congrArg (P m).map (funext restrict_id)).trans Measure.map_id
  | succ n hmn ih =>
    -- The inclusion `Fin m → Fin (n + 1)` factors through `Fin n`.
    have hfac : restrict (L := L) (Fin.castLE (hmn.trans n.le_succ)) =
        restrict (Fin.castLE hmn) ∘ restrict Fin.castSucc := by
      have hcomp : Fin.castLE (hmn.trans n.le_succ) = Fin.castSucc ∘ Fin.castLE hmn :=
        funext fun i => (Fin.castSucc_castLE hmn i).symm
      funext c
      rw [Function.comp_apply, ← restrict_comp, hcomp]
    rw [hfac, ← Measure.map_map (measurable_restrict _) (measurable_restrict _), hP, ih]

/-- The law of the atoms in `J` under the level-`n` window law, extended by `false` to `ℕ`. -/
private noncomputable def windowAtomLaw (n : ℕ) (J : Finset (Atom L ℕ)) : Measure (∀ _ : J, Bool) :=
  (P n).map fun d => J.restrict (d.extend Fin.val).eval

private theorem measurable_restrict_eval_extend (n : ℕ) (J : Finset (Atom L ℕ)) :
    Measurable fun d : RelationalConfiguration L (Fin n) => J.restrict (d.extend Fin.val).eval :=
  (measurable_restrict_eval J).comp (measurable_extend _)

/-- The law of the atoms in `J` does not depend on the level, as long as the level bounds the
vertices of the atoms of `J`. -/
private theorem windowAtomLaw_eq_of_le
    (hP : ∀ n, (P (n + 1)).map (restrict Fin.castSucc) = P n) {J : Finset (Atom L ℕ)} {m n : ℕ}
    (hJ : ∀ a ∈ J, ∃ b : Atom L (Fin m), b.map Fin.val = a) (hmn : m ≤ n) :
    windowAtomLaw P n J = windowAtomLaw P m J := by
  -- Reading the atoms of `J` at level `n` is reading them on the window below `m`.
  have hread : (fun d : RelationalConfiguration L (Fin n) => J.restrict (d.extend Fin.val).eval) =
      (fun d : RelationalConfiguration L (Fin m) => J.restrict (d.extend Fin.val).eval) ∘
        restrict (Fin.castLE hmn) := by
    funext d
    ext a
    obtain ⟨b, hb⟩ := hJ a a.2
    have hval : (b.map (Fin.castLE hmn)).map Fin.val = b.map (Fin.val : Fin m → ℕ) := by
      -- `Fin.val ∘ Fin.castLE hmn` is `Fin.val` by definition.
      rw [← Atom.map_comp]
      rfl
    simp only [Function.comp_apply, Finset.restrict, ← hb]
    rw [← hval, eval_extend_map Fin.val_injective, hval, eval_extend_map Fin.val_injective,
      eval_restrict]
  rw [windowAtomLaw, windowAtomLaw, ← map_restrict_castLE_of_map_restrict_castSucc P hP hmn,
    Measure.map_map (measurable_restrict_eval_extend m J) (measurable_restrict _), ← hread]

/-- A level bounding the vertices of the atoms in `J`. -/
private noncomputable def atomLevel (J : Finset (Atom L ℕ)) : ℕ :=
  (Atom.exists_forall_map_val J).choose

private theorem atomLevel_spec (J : Finset (Atom L ℕ)) :
    ∀ a ∈ J, ∃ b : Atom L (Fin (atomLevel J)), b.map Fin.val = a :=
  (Atom.exists_forall_map_val J).choose_spec

/-- The window laws prescribe the law of every finite set of atoms. -/
private noncomputable def windowAtomFamily (J : Finset (Atom L ℕ)) : Measure (∀ _ : J, Bool) :=
  windowAtomLaw P (atomLevel J) J

private instance [∀ n, IsProbabilityMeasure (P n)] (J : Finset (Atom L ℕ)) :
    IsProbabilityMeasure (windowAtomFamily P J) := by
  unfold windowAtomFamily windowAtomLaw
  infer_instance

variable {P}

/-- The prescribed law of the atoms in `J` is read off any level bounding their vertices. -/
private theorem windowAtomFamily_eq (hP : ∀ n, (P (n + 1)).map (restrict Fin.castSucc) = P n)
    {J : Finset (Atom L ℕ)} {n : ℕ} (hJ : ∀ a ∈ J, ∃ b : Atom L (Fin n), b.map Fin.val = a) :
    windowAtomFamily P J = windowAtomLaw P n J := by
  rw [windowAtomFamily,
    ← windowAtomLaw_eq_of_le P hP (atomLevel_spec J) (le_max_left (atomLevel J) n),
    windowAtomLaw_eq_of_le P hP hJ (le_max_right _ n)]

private theorem isProjectiveMeasureFamily_windowAtomFamily
    (hP : ∀ n, (P (n + 1)).map (restrict Fin.castSucc) = P n) :
    IsProjectiveMeasureFamily (α := fun _ : Atom L ℕ => Bool) (windowAtomFamily P) := by
  intro I J hJI
  have hI := atomLevel_spec I
  rw [windowAtomFamily_eq hP hI, windowAtomFamily_eq hP fun a ha => hI a (hJI ha), windowAtomLaw,
    windowAtomLaw,
    Measure.map_map (measurable_of_countable _) (measurable_restrict_eval_extend _ I)]
  -- Restricting the atoms in `I` to `J` is restricting to `J` (`restrict₂_comp_restrict`).
  rfl

/-- **Kolmogorov extension for configurations over `ℕ`.** For a language with countably many
relation symbols of each arity, probability laws on the configurations on the windows `Fin n` that
are consistent under restriction along the inclusions `Fin n → Fin (n + 1)` are the windows of a
probability law on the configurations over `ℕ`. This law is unique among finite measures by
`measure_ext_of_map_restrict_val`. -/
theorem exists_map_restrict_val_eq [∀ n, Countable (L.Relations n)]
    [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ n, (P (n + 1)).map (restrict Fin.castSucc) = P n) :
    ∃ ν : Measure (RelationalConfiguration L ℕ), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (restrict (Fin.val : Fin n → ℕ)) = P n := by
  -- Kolmogorov extension of the laws of the atom coordinates, a countable family of Booleans.
  obtain ⟨ν, hν, hlim⟩ := TauCeti.Measure.exists_isProjectiveLimit_of_countable
    (X := fun _ : Atom L ℕ => Bool) (windowAtomFamily P)
    (isProjectiveMeasureFamily_windowAtomFamily hP)
  refine ⟨ν.map mk, inferInstance, fun n => ?_⟩
  have hid : restrict (L := L) (Fin.val : Fin n → ℕ) ∘ extend Fin.val = id :=
    funext (restrict_extend Fin.val_injective)
  -- The window law is the window of its own extension by `false`; compare atom by atom.
  rw [← Measure.map_id (μ := P n), ← hid,
    ← Measure.map_map (measurable_restrict _) (measurable_extend _)]
  refine map_restrict_eq_of_forall_finset _ fun J hJ => ?_
  have hread : ((fun c : RelationalConfiguration L ℕ => J.restrict c.eval) ∘ mk) = J.restrict :=
    funext fun x => funext fun a => eval_mk x a
  rw [Measure.map_map (measurable_restrict_eval J) measurable_mk, hread, hlim J,
    windowAtomFamily_eq hP hJ, windowAtomLaw,
    Measure.map_map (measurable_restrict_eval J) (measurable_extend _)]
  -- Both sides read the atoms of `J` off the extension, once through `Function.comp`.
  rfl

end Extension

end RelationalConfiguration

end TauCeti
