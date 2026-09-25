/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FundamentalGroup
public import TauCeti.Combinatorics.PermutationTriple.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# The monodromy triple of a cover of the thrice-punctured sphere

A covering map `p : E → U` of the thrice-punctured sphere `U = ℂ ∖ {0, 1}` whose fibre over the
basepoint `b = 1/2` is numbered, `ν : p ⁻¹' {b} ≃ Fin n`, has a permutation triple: the monodromy
permutations of the numbered fibre along the three peripheral elements `periph0`, `periph1`,
`periphInf` of `π₁(U, b)`,

  `σ_i = ν.permCongr (monodromy of periph_i)`.

Monodromy is a homomorphism `π₁(U, b) →* Equiv.Perm (p ⁻¹' {b})` with no `ᵐᵒᵖ`
(`IsCoveringMap.monodromyPerm`), so the relation `periphInf * periph1 * periph0 = 1` becomes the
relation `σinf * σ1 * σ0 = 1` of a permutation triple on the nose.

The construction factors through representations. Any homomorphism
`ρ : π₁(U, b) →* Equiv.Perm (Fin n)` has the triple `(ρ periph0, ρ periph1, ρ periphInf)`, and since
`periph0` and `periph1` generate `π₁(U, b)`, that triple determines `ρ`, its monodromy group is the
image of `ρ`, and conjugating `ρ` relabels it.

For a cover, the triple records the cover faithfully in the following senses.

* It is connected exactly when the total space is path connected: path lifting identifies the
  monodromy orbits on the fibre with the path components of `E`, and a nonempty fibre is the
  same as a nonempty total space.
* It is unchanged by a map of covers over `U` that respects the numberings.
* Renumbering the fibre by a permutation `τ` relabels the triple by `τ`. Hence the
  isomorphism class of the triple does not depend on the numbering, and is an invariant of the
  cover up to homeomorphism over `U`.

## Main declarations

* `TauCeti.ThricePuncturedSphere.permutationTriple`: the triple of a representation of
  `π₁(U, b)` on `Fin n`, with `monodromyGroup_permutationTriple`,
  `isConnected_permutationTriple_iff`, `permutationTriple_conj` and
  `permutationTriple_injective`.
* `IsCoveringMap.monodromyTriple`: the monodromy triple of a cover of `U` with numbered fibre,
  with its components `monodromyTriple_σ0`, `monodromyTriple_σ1`, `monodromyTriple_σinf`.
* `IsCoveringMap.isConnected_monodromyTriple_iff`: the triple is connected exactly when the total
  space is path connected.
* `IsCoveringMap.monodromyTriple_eq_of_comp_eq`: a map of covers respecting the numberings
  preserves the triple.
* `IsCoveringMap.monodromyTriple_trans`: renumbering the fibre relabels the triple.
* `IsCoveringMap.isoClass_monodromyTriple_eq` and
  `IsCoveringMap.isoClass_monodromyTriple_eq_of_homeomorph`: the isomorphism class of the triple
  depends only on the cover up to homeomorphism over `U`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7 (the monodromy of a cover, well defined up to the numbering of the fibre). That text
  multiplies paths in the opposite order and so inverts the monodromy permutations; with Mathlib's
  order no inversion is needed, and the resulting triples are the componentwise inverses of the
  ones there.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the action of the
  fundamental group on a fibre).
-/

public section

open Equiv Function

universe u

namespace TauCeti

namespace ThricePuncturedSphere

variable {n : ℕ}

/-! ### The triple of a representation of the fundamental group -/

/-- The permutation triple of a representation `ρ` of `π₁(ℂ ∖ {0, 1}, 1/2)` on `Fin n`: its values
at the peripheral elements `periph0` and `periph1`, the third component being `ρ periphInf`
(`permutationTriple_σinf`). -/
noncomputable def permutationTriple
    (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Perm (Fin n)) : PermutationTriple n :=
  PermutationTriple.ofTwo (ρ periph0) (ρ periph1)

variable (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Perm (Fin n))

@[simp]
theorem permutationTriple_σ0 : (permutationTriple ρ).σ0 = ρ periph0 :=
  (rfl)

@[simp]
theorem permutationTriple_σ1 : (permutationTriple ρ).σ1 = ρ periph1 :=
  (rfl)

/-- The third component of the triple of `ρ` is the value of `ρ` at the peripheral element at
`∞`. -/
@[simp]
theorem permutationTriple_σinf : (permutationTriple ρ).σinf = ρ periphInf := by
  rw [periphInf_def, map_inv, map_mul]
  exact PermutationTriple.ofTwo_σinf _ _

/-- The monodromy group of the triple of `ρ` is the image of `ρ`, because `periph0` and
`periph1` generate the fundamental group. -/
theorem monodromyGroup_permutationTriple : (permutationTriple ρ).monodromyGroup = ρ.range := by
  rw [← PermutationTriple.closure_pair_eq_monodromyGroup, permutationTriple_σ0,
    permutationTriple_σ1, ← Set.image_pair, ← MonoidHom.map_closure, closure_periph0_periph1,
    MonoidHom.range_eq_map]

/-- The triple of `ρ` is connected exactly when `n ≠ 0` and the image of `ρ` acts transitively on
`Fin n`. -/
theorem isConnected_permutationTriple_iff :
    (permutationTriple ρ).IsConnected ↔
      n ≠ 0 ∧ MulAction.IsPretransitive ρ.range (Fin n) := by
  rw [PermutationTriple.isConnected_iff, monodromyGroup_permutationTriple]

/-- Conjugating a representation by `τ` relabels its triple by `τ`. -/
theorem permutationTriple_conj (τ : Perm (Fin n)) :
    permutationTriple ((MulAut.conj τ).toMonoidHom.comp ρ) = τ • permutationTriple ρ :=
  PermutationTriple.ext_of_two rfl rfl

/-- A representation of `π₁(ℂ ∖ {0, 1}, 1/2)` is determined by its triple. -/
theorem permutationTriple_injective :
    Injective (permutationTriple : (FundamentalGroup ThricePuncturedSphere basePt →*
      Perm (Fin n)) → PermutationTriple n) := fun _ _ h =>
  fundamentalGroup_hom_ext (congrArg PermutationTriple.σ0 h) (congrArg PermutationTriple.σ1 h)

end ThricePuncturedSphere

/-! ### The monodromy triple of a cover -/

open ThricePuncturedSphere

variable {n : ℕ} {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
  {p : E → ThricePuncturedSphere} {q : F → ThricePuncturedSphere}

/-- The monodromy triple of a covering map `p : E → ℂ ∖ {0, 1}` whose fibre over the basepoint
`1/2` is numbered by `ν`: the monodromy permutations of the numbered fibre along the peripheral
elements `periph0`, `periph1` and `periphInf`. -/
noncomputable def _root_.IsCoveringMap.monodromyTriple (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) : PermutationTriple n :=
  permutationTriple (ν.permCongrHom.toMonoidHom.comp (hp.monodromyPerm basePt))

variable (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

theorem _root_.IsCoveringMap.monodromyTriple_def :
    hp.monodromyTriple ν =
      permutationTriple (ν.permCongrHom.toMonoidHom.comp (hp.monodromyPerm basePt)) :=
  (rfl)

@[simp]
theorem _root_.IsCoveringMap.monodromyTriple_σ0 :
    (hp.monodromyTriple ν).σ0 = ν.permCongr (hp.monodromyPerm basePt periph0) :=
  (rfl)

@[simp]
theorem _root_.IsCoveringMap.monodromyTriple_σ1 :
    (hp.monodromyTriple ν).σ1 = ν.permCongr (hp.monodromyPerm basePt periph1) :=
  (rfl)

/-- The third component of the monodromy triple is the monodromy along the peripheral element at
`∞`. -/
@[simp]
theorem _root_.IsCoveringMap.monodromyTriple_σinf :
    (hp.monodromyTriple ν).σinf = ν.permCongr (hp.monodromyPerm basePt periphInf) := by
  simp [IsCoveringMap.monodromyTriple_def]

/-- The monodromy group of the monodromy triple is the image of the monodromy representation,
transported to `Fin n` by the numbering. -/
theorem _root_.IsCoveringMap.monodromyGroup_monodromyTriple :
    (hp.monodromyTriple ν).monodromyGroup =
      (hp.monodromyPerm basePt).range.map ν.permCongrHom.toMonoidHom := by
  rw [IsCoveringMap.monodromyTriple_def, monodromyGroup_permutationTriple, MonoidHom.range_comp]

/-- The monodromy triple is connected exactly when the total space of the cover is path
connected. -/
theorem _root_.IsCoveringMap.isConnected_monodromyTriple_iff :
    (hp.monodromyTriple ν).IsConnected ↔ PathConnectedSpace E := by
  rw [IsCoveringMap.monodromyTriple_def, isConnected_permutationTriple_iff]
  -- Transitivity of the image on `Fin n` is transitivity of monodromy on the numbered fibre.
  have htrans : MulAction.IsPretransitive
      (ν.permCongrHom.toMonoidHom.comp (hp.monodromyPerm basePt)).range (Fin n) ↔
      ∀ e e' : p ⁻¹' {basePt}, ∃ γ : FundamentalGroup ThricePuncturedSphere basePt,
        hp.monodromy γ e = e' := by
    refine ⟨fun ⟨h⟩ e e' => ?_, fun h => ⟨fun i j => ?_⟩⟩
    · obtain ⟨⟨_, γ, rfl⟩, hγ⟩ := h (ν e) (ν e')
      rw [Subgroup.smul_def, Perm.smul_def] at hγ
      exact ⟨γ, ν.injective (by simpa [permCongr_apply] using hγ)⟩
    · obtain ⟨γ, hγ⟩ := h (ν.symm i) (ν.symm j)
      refine ⟨⟨_, γ, rfl⟩, ?_⟩
      rw [Subgroup.smul_def]
      simp [permCongr_apply, hγ]
  have hn : n ≠ 0 ↔ Nonempty (p ⁻¹' {basePt}) := by
    rw [ν.nonempty_congr, ← Fin.pos_iff_nonempty, Nat.pos_iff_ne_zero]
  rw [htrans, hn, hp.pathConnectedSpace_iff basePt]

/-- The monodromy triple of a cover with path-connected total space is connected. -/
theorem _root_.IsCoveringMap.isConnected_monodromyTriple [PathConnectedSpace E] :
    (hp.monodromyTriple ν).IsConnected :=
  (hp.isConnected_monodromyTriple_iff ν).2 ‹_›

/-- A map of covers over `ℂ ∖ {0, 1}` carrying the point numbered `i` of the first fibre to the
point numbered `i` of the second has the same monodromy triple on both sides. -/
theorem _root_.IsCoveringMap.monodromyTriple_eq_of_comp_eq (hq : IsCoveringMap q)
    (ν' : q ⁻¹' {basePt} ≃ Fin n) (f : C(E, F)) (hf : q ∘ f = p)
    (hν : ∀ e, ν' (fiberMap f hf basePt e) = ν e) :
    hq.monodromyTriple ν' = hp.monodromyTriple ν := by
  have key : ∀ γ : FundamentalGroup ThricePuncturedSphere basePt,
      ν'.permCongr (hq.monodromyPerm basePt γ) = ν.permCongr (hp.monodromyPerm basePt γ) := by
    intro γ
    ext i
    obtain ⟨e, rfl⟩ := ν.surjective i
    rw [permCongr_apply, permCongr_apply, symm_apply_apply, ← hν e, symm_apply_apply,
      IsCoveringMap.coe_monodromyPerm, IsCoveringMap.coe_monodromyPerm,
      ← hp.fiberMap_monodromy hq f hf γ e, hν]
  exact PermutationTriple.ext_of_two (key periph0) (key periph1)

/-- Renumbering the fibre by a permutation `τ` of `Fin n` relabels the monodromy triple by `τ`. -/
theorem _root_.IsCoveringMap.monodromyTriple_trans (τ : Perm (Fin n)) :
    hp.monodromyTriple (ν.trans τ) = τ • hp.monodromyTriple ν := by
  refine PermutationTriple.ext_of_two ?_ ?_ <;>
  · ext i
    simp [permCongr_apply]

/-- The isomorphism class of the monodromy triple does not depend on the numbering of the
fibre. -/
theorem _root_.IsCoveringMap.isoClass_monodromyTriple_eq (ν' : p ⁻¹' {basePt} ≃ Fin n) :
    PermutationTriple.IsoClass.mk (hp.monodromyTriple ν') =
      PermutationTriple.IsoClass.mk (hp.monodromyTriple ν) := by
  have : ν' = ν.trans (ν.symm.trans ν') := by ext; simp
  rw [this, hp.monodromyTriple_trans, PermutationTriple.IsoClass.mk_eq_mk_iff]
  exact PermutationTriple.equivalent_smul _ _

/-- Covers of `ℂ ∖ {0, 1}` that are homeomorphic over `ℂ ∖ {0, 1}` have isomorphic monodromy
triples, whatever the numberings of their fibres. -/
theorem _root_.IsCoveringMap.isoClass_monodromyTriple_eq_of_homeomorph (hq : IsCoveringMap q)
    (ν' : q ⁻¹' {basePt} ≃ Fin n) (f : E ≃ₜ F) (hf : q ∘ f = p) :
    PermutationTriple.IsoClass.mk (hq.monodromyTriple ν') =
      PermutationTriple.IsoClass.mk (hp.monodromyTriple ν) := by
  -- Transport the numbering of the fibre of `p` along `f`, and compare with it.
  let φ : p ⁻¹' {basePt} ≃ q ⁻¹' {basePt} :=
    f.toEquiv.subtypeEquiv fun e => by simp [← hf]
  have hφ : ∀ e, φ e = fiberMap (f : C(E, F)) hf basePt e := fun e =>
    Subtype.ext (fiberMap_apply_coe _ hf basePt e).symm
  rw [hq.isoClass_monodromyTriple_eq (φ.symm.trans ν) ν',
    hp.monodromyTriple_eq_of_comp_eq ν hq (φ.symm.trans ν) f hf fun e => by
      rw [trans_apply, ← hφ, symm_apply_apply]]

end TauCeti
