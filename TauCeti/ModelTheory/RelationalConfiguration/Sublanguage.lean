/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
public import TauCeti.ModelTheory.Sublanguage

/-!
# Relational configurations on symbol sublanguages

For a symbol sublanguage `L.symbSublang F R` with inclusion
`symbSublangIncl F R : L.symbSublang F R →ᴸ L`, the reduct map
`(symbSublangIncl F R).reductConfiguration` restricts a configuration on `V` to the atoms whose
relation symbols lie in `R`.

Because `RelationalConfiguration L V` carries the product σ-algebra over all atoms and countable
unions of countable symbol sets remain countable, every measurable set of configurations of `L` on
`V` factors as the preimage under `(symbSublangIncl F R).reductConfiguration` of a measurable set on
`L.symbSublang F R` for some countable set `R` of relation symbols
(`exists_countable_sublanguage_measurableSet`), without assuming that `L` is relational or that `V`
is countable.

## Main results

* `TauCeti.RelationalConfiguration.exists_countable_sublanguage_measurableSet`: every measurable set
  of configurations in the product σ-algebra is the preimage of a measurable set on a symbol
  sublanguage with countably many relation symbols.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w}

private theorem measurableSet_generateFrom_setOf_eval
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    MeasurableSet[MeasurableSpace.generateFrom
      (range fun a : Atom L V => {c : RelationalConfiguration L V | c.eval a = true})] C := by
  let m : MeasurableSpace (RelationalConfiguration L V) :=
    MeasurableSpace.generateFrom
      (range fun a : Atom L V => {c : RelationalConfiguration L V | c.eval a = true})
  refine (@measurable_iff L V _ m id).2 (fun a s _ => ?_) hC
  have heq : (fun ω : RelationalConfiguration L V => (id ω).eval a) ⁻¹' s =
      ({c | c.eval a = true} ∩ {_c | true ∈ s}) ∪
        ({c | c.eval a = true}ᶜ ∩ {_c | false ∈ s}) := by
    ext c
    rcases Bool.dichotomy (c.eval a) with hb | hb <;> simp [hb]
  rw [heq]
  have ha : MeasurableSet[m] {c : RelationalConfiguration L V | c.eval a = true} :=
    MeasurableSpace.measurableSet_generateFrom ⟨a, rfl⟩
  exact (ha.inter (.const _)).union (ha.compl.inter (.const _))

/-- Every measurable set of configurations in the product σ-algebra factors as the preimage under
`(symbSublangIncl F R).reductConfiguration` of a measurable set on a symbol sublanguage
`L.symbSublang F R` with `R` countable. Neither `L.IsRelational` nor `Countable V` is assumed. -/
theorem exists_countable_sublanguage_measurableSet (F : Set (Σ n, L.Functions n))
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      ∃ C₀ : Set (RelationalConfiguration (L.symbSublang F R) V),
        MeasurableSet C₀ ∧ (symbSublangIncl F R).reductConfiguration ⁻¹' C₀ = C := by
  have hgen := measurableSet_generateFrom_setOf_eval hC
  clear hC
  induction C, hgen using MeasurableSpace.generateFrom_induction with
  | hC B hB _ =>
    obtain ⟨a, rfl⟩ := hB
    induction a using Atom.induction_atom with
    | @h n r tup =>
      refine ⟨{⟨n, r⟩}, countable_singleton _,
        {c₀ | c₀.eval (atom ⟨r, mem_singleton _⟩ tup) = true},
        measurableSet_setOf_eval _ true, ?_⟩
      ext c
      simp
  | empty => exact ⟨∅, countable_empty, ∅, MeasurableSet.empty, rfl⟩
  | compl B _ ih =>
    obtain ⟨R, hR, C₀, hC₀, rfl⟩ := ih
    exact ⟨R, hR, C₀ᶜ, hC₀.compl, rfl⟩
  | iUnion f _ ih =>
    choose R hR C₀ hC₀ hf_eq using ih
    have hex (k : ℕ) : ∃ j : L.symbSublang F (R k) →ᴸ L.symbSublang F (⋃ i, R i),
        (symbSublangIncl F (⋃ i, R i)).comp j = symbSublangIncl F (R k) :=
      (symbSublangIncl F (⋃ i, R i)).exists_comp_eq_symbSublangIncl
        (fun s hs => ⟨⟨s.1, ⟨s.2, hs⟩⟩, by simp⟩)
        (fun s hs => ⟨⟨s.1, ⟨s.2, mem_iUnion_of_mem k hs⟩⟩, by simp⟩)
    choose j hj using hex
    refine ⟨⋃ i, R i, countable_iUnion hR,
      ⋃ k, (j k).reductConfiguration ⁻¹' C₀ k,
      MeasurableSet.iUnion fun k => (j k).measurable_reductConfiguration (hC₀ k), ?_⟩
    ext c
    simp only [mem_preimage, mem_iUnion, ← LHom.comp_reductConfiguration, hj, ← hf_eq]

end TauCeti.RelationalConfiguration
