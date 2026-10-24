/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Option
public import TauCeti.GroupTheory.Amenable.Finite
public import TauCeti.Topology.Algebra.Group.UCB.Prod

/-!
# Products of amenable groups

For means `m` on `TauCeti.UCB G` and `n` on `TauCeti.UCB H`, the *iterated mean*

```text
(m.prod n) f = m (x ↦ n (y ↦ f (x, y)))
```

is a mean on `UCB (G × H)`; the inner function lies in `UCB G` by
`TauCeti.UCB.applyRight`. Its marginals are `m` and `n`. If `m` and `n` are left invariant, so is
`m.prod n`: translating `f` by `(g, h)` translates the slice `f (x, ·)` by `h`, which `n` does not
see, and then translates the function `x ↦ n (f (x, ·))` by `g`, which `m` does not see.

Hence the product of two amenable topological groups is amenable, and conversely each factor of an
amenable product is amenable, as an image under a projection. By induction on the index type, the
product of a finite family of amenable topological groups is amenable, the empty product being the
trivial group.

No discreteness is needed: the factors are arbitrary topological groups, and the product carries the
product topology. A finite product of discrete groups is again discrete, so this covers finite
products of discrete groups.

## Main definitions

* `TauCeti.Mean.prod m n`: the iterated mean `f ↦ m (x ↦ n (f (x, ·)))` on `UCB (G × H)`.

## Main results

* `TauCeti.Mean.map_fst_prod`, `TauCeti.Mean.map_snd_prod`: the marginals of `m.prod n` are `m` and
  `n`.
* `TauCeti.Mean.IsLeftInvariant.prod`: the iterated mean of left-invariant means is left invariant.
* `TauCeti.Amenable.prod`: the product of two amenable topological groups is amenable.
* `TauCeti.amenable_prod_iff`: a product of two topological groups is amenable exactly when both
  factors are.
* `TauCeti.Amenable.pi`: the product of a finite family of amenable topological groups is amenable.
* `TauCeti.amenable_pi_iff`: a finite product of topological groups is amenable exactly when every
  factor is.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

universe u v

namespace TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

namespace Mean

/-- The iterated mean `f ↦ m (x ↦ n (f (x, ·)))` on `UCB (G × H)` of means `m` on `UCB G` and `n`
on `UCB H`. -/
def prod (m : Mean G) (n : Mean H) : Mean (G × H) :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ
      (UCB.applyRight (G := G) n.toContinuousLinearMap).toLinearMap)
    (fun f hf => map_nonneg m <| UCB.le_def.2 fun x => by
      simpa using map_nonneg n (by simpa using UCB.monotone_compProdMk x hf))
    (by simp)

/-- The iterated mean formula: `(m.prod n) f = m (x ↦ n (f (x, ·)))`. -/
@[simp]
theorem prod_apply (m : Mean G) (n : Mean H) (f : UCB (G × H)) :
    m.prod n f = m (UCB.applyRight n.toContinuousLinearMap f) :=
  mk₀_apply _ _ _ f

/-- The first marginal of `m.prod n` is `m`. -/
@[simp]
theorem map_fst_prod (m : Mean G) (n : Mean H) :
    (m.prod n).map (ContinuousMonoidHom.fst G H) = m :=
  ext fun f => by simp

/-- The second marginal of `m.prod n` is `n`. -/
@[simp]
theorem map_snd_prod (m : Mean G) (n : Mean H) :
    (m.prod n).map (ContinuousMonoidHom.snd G H) = n :=
  ext fun f => by simp

/-- The iterated mean of left-invariant means is left invariant. -/
theorem IsLeftInvariant.prod {m : Mean G} {n : Mean H} (hm : m.IsLeftInvariant)
    (hn : n.IsLeftInvariant) : (m.prod n).IsLeftInvariant :=
  isLeftInvariant_iff.2 fun p f => by
    rw [prod_apply, prod_apply,
      UCB.applyRight_leftTranslation _ (fun h f => by simpa using hn.apply_leftTranslation h f),
      hm.apply_leftTranslation]

end Mean

/-- The product of two amenable topological groups is amenable. -/
instance Amenable.prod [Amenable G] [Amenable H] : Amenable (G × H) :=
  have ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  have ⟨n, hn⟩ := Amenable.exists_isLeftInvariant (G := H)
  ⟨⟨m.prod n, hm.prod hn⟩⟩

variable (G H) in
/-- A product of two topological groups is amenable exactly when both factors are. -/
theorem amenable_prod_iff : Amenable (G × H) ↔ Amenable G ∧ Amenable H :=
  ⟨fun _ => ⟨.of_surjective (ContinuousMonoidHom.fst G H) Prod.fst_surjective,
      .of_surjective (ContinuousMonoidHom.snd G H) Prod.snd_surjective⟩,
    fun ⟨_, _⟩ => inferInstance⟩

/-- The product of a finite family of amenable topological groups is amenable. -/
instance Amenable.pi {ι : Type u} [Finite ι] {G : ι → Type v} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, Amenable (G i)] :
    Amenable (∀ i, G i) := by
  refine Finite.induction_empty_option (P := fun ι => ∀ (G : ι → Type v) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, Amenable (G i)],
      Amenable (∀ i, G i)) ?_ ?_ ?_ ι G
  · -- Reindex along `e : α ≃ β` by the cast isomorphism `(∀ a, G (e a)) ≃ (∀ b, G b)`.
    intro α β e h G _ _ _ _
    have := h (fun a => G (e a))
    let φ : (∀ a, G (e a)) →ₜ* ∀ b, G b :=
      { toFun := Equiv.piCongrLeft G e
        map_one' := funext fun b => by
          obtain ⟨a, rfl⟩ := e.surjective b
          simp [Equiv.piCongrLeft_apply_apply]
        map_mul' f f' := funext fun b => by
          obtain ⟨a, rfl⟩ := e.surjective b
          simp [Equiv.piCongrLeft_apply_apply]
        continuous_toFun := (Homeomorph.piCongrLeft e).continuous }
    exact .of_surjective φ (Equiv.piCongrLeft G e).surjective
  · -- The empty product is the trivial group.
    intro G _ _ _ _
    infer_instance
  · -- `∀ o : Option α, G o` is the image of `G none × ∀ a, G (some a)`.
    intro α _ h G _ _ _ _
    have := h (fun a => G (some a))
    let φ : (G none × ∀ a, G (some a)) →ₜ* ∀ o, G o :=
      { toFun := Equiv.piOptionEquivProd.symm
        map_one' := funext fun o => by cases o <;> rfl
        map_mul' _ _ := funext fun o => by cases o <;> rfl
        continuous_toFun := continuous_pi fun o => by
          -- By definition, the `none` component of `piOptionEquivProd.symm p` is `p.1`, and its
          -- `some a` component is `p.2 a`.
          cases o
          exacts [continuous_fst,
            ((continuous_apply _).comp continuous_snd :
              Continuous fun p : G none × ∀ a, G (some a) => p.2 _)] }
    exact .of_surjective φ Equiv.piOptionEquivProd.symm.surjective

/-- A product of a finite family of topological groups is amenable exactly when every factor
is. -/
theorem amenable_pi_iff {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] :
    Amenable (∀ i, G i) ↔ ∀ i, Amenable (G i) :=
  ⟨fun _ i => .of_surjective ⟨Pi.evalMonoidHom G i, continuous_apply i⟩
      (Function.surjective_eval i),
    fun _ => inferInstance⟩

end TauCeti
