/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Finitely presented compactifications

A compactification `(Xbar, j, p)` of a scheme morphism `f` is finitely presented when its proper
map `p` is locally of finite presentation. Being proper, `p` is also quasi-compact and
quasi-separated, so `p` is then of finite presentation. These compactifications form the full
subcategory `TauCeti.FPCompactification f` of `TauCeti.Compactification f`, which is closed under
isomorphism; its inclusion is `ObjectProperty.ι`.

Finite type does not replace finite presentation here. For an ideal `J` of a ring `A`, the
closed immersion `Spec (A ⧸ J) ⟶ Spec A` is proper, so it is its own compactification. This
compactification is finitely presented exactly when `J` is finitely generated
(`TauCeti.Compactification.fpCompactificationProperty_identity_quotient_iff`).

Only a morphism locally of finite presentation has a finitely presented compactification
(`TauCeti.FPCompactification.locallyOfFinitePresentation`). Every morphism of compactifications
out of a finitely presented one has a map of ambient schemes locally of finite presentation,
whatever its target (`TauCeti.Compactification.Hom.locallyOfFinitePresentation`). Base change
along any morphism of bases preserves finitely presented compactifications
(`TauCeti.FPCompactification.baseChangeFunctor`), with the open immersion and proper map of the
underlying base change.

## Main definitions

* `TauCeti.fpCompactificationProperty f`: the compactifications of `f` whose proper map is
  locally of finite presentation.
* `TauCeti.FPCompactification f`: the full subcategory of finitely presented compactifications.
* `TauCeti.FPCompactification.baseChangeFunctor g`: base change along `g` on finitely presented
  compactifications.

## References

* B. Zavyalov, *Mod-p Poincaré duality in p-adic analytic geometry*, Definition 2.1.1.
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S T : Scheme.{u}} (f : X ⟶ S)

/-- Compactifications whose proper map is locally of finite presentation. -/
def fpCompactificationProperty : ObjectProperty (Compactification f) :=
  fun C ↦ LocallyOfFinitePresentation C.p

@[simp]
theorem fpCompactificationProperty_iff (C : Compactification f) :
    fpCompactificationProperty f C ↔ LocallyOfFinitePresentation C.p :=
  (Iff.rfl)

/-- Finite presentation of a compactification is invariant under isomorphism. -/
instance : (fpCompactificationProperty f).IsClosedUnderIsomorphisms where
  of_iso {C D} e hC := by
    rw [fpCompactificationProperty_iff] at hC ⊢
    rw [Compactification.p, ← e.inv.hom.h_π]
    infer_instance

/-- The full subcategory of compactifications whose proper map is locally of finite
presentation. -/
abbrev FPCompactification := (fpCompactificationProperty f).FullSubcategory

namespace Compactification

variable {f}

/-- A morphism of compactifications out of a finitely presented one has a map of ambient
schemes locally of finite presentation; the target need not be finitely presented. -/
instance Hom.locallyOfFinitePresentation {C D : Compactification f} (h : C ⟶ D)
    [LocallyOfFinitePresentation C.p] : LocallyOfFinitePresentation h.hom.h := by
  have : LocallyOfFinitePresentation (h.hom.h ≫ D.p) := by
    rw [h.hom.h_π]
    infer_instance
  exact locallyOfFinitePresentation_of_comp h.hom.h D.p

/-- Base change preserves finite presentation of a compactification. -/
instance baseChange_locallyOfFinitePresentation (C : Compactification f)
    [LocallyOfFinitePresentation C.p] (g : T ⟶ S) :
    LocallyOfFinitePresentation (C.baseChange g).p := by
  rw [baseChange_p]
  infer_instance

/-- For an ideal `J` of `A`, the proper closed immersion `Spec (A ⧸ J) ⟶ Spec A` is its own
compactification, and this compactification is finitely presented exactly when `J` is finitely
generated. So a compactification whose proper map is of finite type need not be finitely
presented. -/
theorem fpCompactificationProperty_identity_quotient_iff {A : CommRingCat.{u}} (J : Ideal A) :
    fpCompactificationProperty _
        (identity (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ↔ J.FG := by
  simp only [fpCompactificationProperty_iff, ofHom_obj_π, LocallyOfFinitePresentation.SpecMap_iff,
    CommRingCat.hom_ofHom]
  refine ⟨fun h ↦ ?_, fun h ↦ .of_surjective _ Ideal.Quotient.mk_surjective (by
    rwa [Ideal.mk_ker])⟩
  rw [← Ideal.Quotient.algebraMap_eq, RingHom.finitePresentation_algebraMap] at h
  have := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ A J)
    (Ideal.Quotient.mkₐ_surjective A J)
  rwa [AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker] at this

end Compactification

namespace FPCompactification

variable {f}

instance (C : FPCompactification f) : LocallyOfFinitePresentation C.obj.p := C.property

/-- Bundle a quasi-compact open immersion and a proper map locally of finite presentation as a
finitely presented compactification. -/
@[simps obj]
abbrev ofHom {Y : Scheme.{u}} (j : X ⟶ Y) (p : Y ⟶ S) [IsOpenImmersion j] [QuasiCompact j]
    [IsProper p] [LocallyOfFinitePresentation p] (fac : j ≫ p = f) : FPCompactification f :=
  ⟨Compactification.ofHom j p fac, (fpCompactificationProperty_iff f _).mpr ‹_›⟩

/-- A morphism with a finitely presented compactification is locally of finite presentation. -/
theorem locallyOfFinitePresentation (C : FPCompactification f) :
    LocallyOfFinitePresentation f := by
  rw [← C.obj.obj.ι_π]
  infer_instance

/-- Pull back a finitely presented compactification along an arbitrary map of bases. -/
@[simps obj]
noncomputable abbrev baseChange (C : FPCompactification f) (g : T ⟶ S) :
    FPCompactification (pullback.snd f g) :=
  ⟨C.obj.baseChange g, (fpCompactificationProperty_iff _ _).mpr inferInstance⟩

/-- Base change on the full subcategories of finitely presented compactifications. -/
-- The underlying morphism formula needs definitionally matching endpoints under `simp`.
@[expose, implicit_reducible] noncomputable def baseChangeFunctor (g : T ⟶ S) :
    FPCompactification f ⥤ FPCompactification (pullback.snd f g) :=
  (fpCompactificationProperty (pullback.snd f g)).lift
    ((fpCompactificationProperty f).ι ⋙ Compactification.baseChangeFunctor g)
    (fun C ↦ (C.baseChange g).property)

@[simp]
theorem baseChangeFunctor_obj_obj (g : T ⟶ S) (C : FPCompactification f) :
    ((baseChangeFunctor g).obj C).obj = C.obj.baseChange g :=
  (rfl)

@[simp]
theorem baseChangeFunctor_map_hom (g : T ⟶ S) {C D : FPCompactification f} (h : C ⟶ D) :
    ((baseChangeFunctor g).map h).hom = Compactification.baseChangeMap h.hom g :=
  (rfl)

variable (f)

/-- The identity compactification of a proper morphism locally of finite presentation, for
instance of any morphism out of the empty scheme. -/
@[simps obj]
abbrev identity [IsProper f] [LocallyOfFinitePresentation f] : FPCompactification f :=
  ⟨Compactification.identity f, (fpCompactificationProperty_iff f _).mpr ‹_›⟩

end FPCompactification

end TauCeti
