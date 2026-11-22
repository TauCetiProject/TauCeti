/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Sheaves.KSheaf
public import TauCeti.Topology.Sets.Compacts

/-!
# Pushforward of K-sheaves along proper maps

A K-presheaf on a space `X` (`TopCat.KPresheaf`) is a contravariant functor on the compact
subsets of `X`. A proper map `f : X ⟶ Y` pulls compact subsets of `Y` back to compact subsets of
`X` (`TopologicalSpace.Compacts.comap`), so a K-presheaf `P` on `X` pushes forward to the
K-presheaf `f_* P` on `Y` with

`(f_* P)(K) = P(f⁻¹(K))`

(`TopCat.KPresheaf.pushforward`). This file proves that pushforward preserves K-sheaves when `X`
and `Y` are Hausdorff and `Y` is locally compact (`TopCat.KPresheaf.IsKSheaf.pushforward`), which
is the K-sheaf case of Pardon's Lemma A.3.3. Taking preimages preserves `⊥`, `⊔` and `⊓`, so
the first two K-sheaf axioms for `f_* P` are those of `P` at the preimages. The third, that
`(f_* P)(K)` is the colimit of `(f_* P)(L)` over the compact neighbourhoods `L` of `K`, rests on
the preimages of these `L` being cofinal among the compact neighbourhoods of `f⁻¹(K)`
(`TopologicalSpace.Compacts.exists_comap_le_of_mem_compactNhds`).

Local compactness of `Y` is needed. In `ℚ` the compact set `{0}` has no compact neighbourhood,
so the third axiom at `{0}` asks for an initial object; but the inclusion `{0} → ℚ` is proper,
and the pushforward along it of a K-sheaf on the point takes its value at the point there.

Pushforward of K-sheaves is the functor `TopCat.KSheaf.pushforward`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.3, Lemma A.3.3 and
  Definition A.3.4.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

variable {A : Type u} [Category.{v} A] {X Y : TopCat.{w}}

namespace KPresheaf

/-- The pushforward of K-presheaves along a proper map `f : X ⟶ Y`: the value of the pushforward
of `P` on a compact `K ⊆ Y` is the value of `P` on the compact preimage `f⁻¹(K)`. -/
def pushforward (f : X ⟶ Y) (hf : IsProperMap f) : KPresheaf A X ⥤ KPresheaf A Y :=
  (Functor.whiskeringLeft _ _ A).obj (Compacts.comap_mono f hf).functor.op

variable (f : X ⟶ Y) (hf : IsProperMap f)

@[simp]
lemma pushforward_obj_obj (P : KPresheaf A X) (K : (Compacts Y)ᵒᵖ) :
    ((pushforward f hf).obj P).obj K = P.obj (op (Compacts.comap f hf K.unop)) :=
  (rfl)

@[simp]
lemma pushforward_obj_map (P : KPresheaf A X) {K L : (Compacts Y)ᵒᵖ} (g : K ⟶ L) :
    ((pushforward f hf).obj P).map g =
      P.map (opHomOfLE (Compacts.comap_mono f hf (leOfHom g.unop))) :=
  (rfl)

@[simp]
lemma pushforward_map_app {P Q : KPresheaf A X} (φ : P ⟶ Q) (K : (Compacts Y)ᵒᵖ) :
    ((pushforward f hf).map φ).app K = φ.app (op (Compacts.comap f hf K.unop)) :=
  (rfl)

variable [T2Space X] [T2Space Y]

/-- **Pushforward along a proper map preserves K-sheaves** (Pardon, Lemma A.3.3). If `X` and
`Y` are Hausdorff, `Y` is locally compact and `P` is a K-sheaf on `X`, then its pushforward
`K ↦ P(f⁻¹(K))` along a proper map `f : X ⟶ Y` is a K-sheaf on `Y`. -/
theorem IsKSheaf.pushforward [LocallyCompactSpace Y] {P : KPresheaf A X} (hP : P.IsKSheaf) :
    ((KPresheaf.pushforward f hf).obj P).IsKSheaf where
  nonempty_isTerminal := by
    simpa only [pushforward_obj_obj, unop_op, Compacts.comap_bot] using hP.nonempty_isTerminal
  -- The square of the pushforward is, by definition, the square of `P` at the preimages.
  isPullback {K₁ K₂ K₃ K₄} h :=
    hP.isPullback (K₁ := Compacts.comap f hf K₁) (K₄ := Compacts.comap f hf K₄)
      ⟨by rw [← Compacts.comap_sup, h.sup_eq], by rw [← Compacts.comap_inf, h.inf_eq]⟩
  nonempty_isColimit_coconeOfCompacts K := by
    -- The preimages of the compact neighbourhoods of `K`, as compact neighbourhoods of `f⁻¹(K)`.
    let Φ : K.compactNhds → (Compacts.comap f hf K).compactNhds :=
      fun L ↦ ⟨_, Compacts.comap_mem_compactNhds f hf L.property⟩
    have hΦ : Monotone Φ := fun _ _ h ↦ Compacts.comap_mono f hf h
    have : hΦ.functor.Initial := by
      rw [Monotone.initial_functor_iff]
      intro L'
      obtain ⟨L, hL, hle⟩ := Compacts.exists_comap_le_of_mem_compactNhds f hf L'.property
      exact ⟨⟨L, hL⟩, hle⟩
    -- By definition of `pushforward`, the cocone of the pushforward at `K` is the cocone of `P`
    -- at `f⁻¹(K)` whiskered along `Φ`.
    exact ⟨(Functor.Final.isColimitWhiskerEquiv hΦ.functor.op _).symm
      (hP.nonempty_isColimit_coconeOfCompacts _).some⟩

end KPresheaf

namespace KSheaf

variable [T2Space X] [T2Space Y] [LocallyCompactSpace Y]

/-- The pushforward of K-sheaves along a proper map `f : X ⟶ Y` of Hausdorff spaces with `Y`
locally compact: the K-sheaf `K ↦ P(f⁻¹(K))` (`TopCat.KPresheaf.IsKSheaf.pushforward`). -/
def pushforward (f : X ⟶ Y) (hf : IsProperMap f) : KSheaf A X ⥤ KSheaf A Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ KPresheaf.pushforward f hf)
    fun P ↦ P.property.pushforward f hf

variable (f : X ⟶ Y) (hf : IsProperMap f)

@[simp]
lemma pushforward_obj_obj (P : KSheaf A X) :
    ((pushforward f hf).obj P).obj = (KPresheaf.pushforward f hf).obj P.obj :=
  (rfl)

@[simp]
lemma pushforward_map_hom {P Q : KSheaf A X} (φ : P ⟶ Q) :
    ((pushforward f hf).map φ).hom = (KPresheaf.pushforward f hf).map φ.hom :=
  (rfl)

end KSheaf

end TopCat
