/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Basic
public import TauCeti.AlgebraicGeometry.Scheme.ToSpecZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Intrinsic characteristic of schemes

`TauCeti.AlgebraicGeometry.SchemeCharP X p` means that every local ring of `X` has characteristic
`p`. For prime `p` this is equivalent to the vanishing of `p` in global sections, in every
ring of sections, and to the existence of a (necessarily unique) map to `Spec 𝔽_p`.
The empty scheme is included: its section rings are zero rings, so we assert vanishing of
`p` there, not `CharP` of its section rings. Nonempty opens do have characteristic `p`.

The global-sections characterization supplies exactly the hypothesis of
`AlgebraicGeometry.Scheme.frobenius`; no second Frobenius construction is introduced.
Characteristic is inherited along arbitrary scheme morphisms, hence by open restrictions
and arbitrary base changes. The target `Spec 𝔽_p` uses `ULift` to remain in the universe
of `X`.

## References

* The Stacks Project, Section 33.36 (Tag 0CC6), Frobenii.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- A scheme has characteristic `p` if every one of its local rings has characteristic `p`.
In particular the empty scheme has every characteristic. -/
class SchemeCharP (X : Scheme.{u}) (p : ℕ) : Prop where
  charP_stalk (x : X) : CharP (X.presheaf.stalk x) p

attribute [instance] SchemeCharP.charP_stalk

namespace SchemeCharP

variable {X Y : Scheme.{u}} {p : ℕ}

/-- The characteristic vanishes in the ring of sections of every open, even an empty one. -/
theorem natCast_eq_zero (hX : SchemeCharP X p) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  let := hX
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  exact (map_natCast (X.presheaf.germ U x hx).hom p).trans
    ((CharP.cast_eq_zero (X.presheaf.stalk x) p).trans
      (map_zero (X.presheaf.germ U x hx).hom).symm)

/-- On a nonempty open, the ring of sections is nontrivial and has the scheme's
characteristic. No primality assumption is needed in this direction. -/
theorem charP_sections (hX : SchemeCharP X p) (U : X.Opens) [Nonempty U] :
    CharP Γ(X, U) p := by
  let := hX
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  exact ⟨fun n ↦ by
    constructor
    · intro hn
      exact (CharP.cast_eq_zero_iff (X.presheaf.stalk x) p n).mp
        (by simpa using congr((X.presheaf.germ U x hx) $hn))
    · intro hn
      obtain ⟨k, rfl⟩ := hn
      simp [hX.natCast_eq_zero U]⟩

/-- Characteristic is invariant under isomorphism, for every natural characteristic. -/
theorem iff_of_iso (e : X ≅ Y) : SchemeCharP X p ↔ SchemeCharP Y p := by
  constructor
  · intro h
    let := h
    exact ⟨fun y ↦ charP_of_injective_ringHom
      (f := (e.inv.stalkMap y).hom) (ConcreteCategory.bijective_of_isIso _).1 p⟩
  · intro h
    let := h
    exact ⟨fun x ↦ charP_of_injective_ringHom
      (f := (e.hom.stalkMap x).hom) (ConcreteCategory.bijective_of_isIso _).1 p⟩

variable [Fact p.Prime]

/-- For prime `p`, stalkwise characteristic is equivalent to global vanishing of `p`. -/
theorem iff_natCast_eq_zero : SchemeCharP X p ↔ (p : Γ(X, ⊤)) = 0 := by
  refine ⟨fun h ↦ h.natCast_eq_zero ⊤, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  simpa using congr((X.presheaf.germ ⊤ x (by trivial)) $h)

/-- For prime `p`, it suffices, and is necessary, that `p` vanish on every open. -/
theorem iff_forall_natCast_eq_zero :
    SchemeCharP X p ↔ ∀ U : X.Opens, (p : Γ(X, U)) = 0 :=
  ⟨fun h ↦ h.natCast_eq_zero, fun h ↦ iff_natCast_eq_zero.mpr (h ⊤)⟩

/-- Characteristic `p` can be checked on all affine opens. -/
theorem iff_affineOpens : SchemeCharP X p ↔
    ∀ U : X.Opens, IsAffineOpen U → (p : Γ(X, U)) = 0 := by
  refine ⟨fun h U _ ↦ h.natCast_eq_zero U, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  simpa using congr((X.presheaf.germ U x hx) $(h U hU))

/-- A scheme over a characteristic-`p` scheme has characteristic `p`. -/
theorem of_hom (hY : SchemeCharP Y p) (f : X ⟶ Y) : SchemeCharP X p :=
  iff_natCast_eq_zero.mpr (Scheme.natCast_eq_zero_of_hom f (hY.natCast_eq_zero ⊤))

/-- The spectrum of a ring has characteristic `p` exactly when `p` vanishes in the ring.
This also applies to the zero ring. -/
theorem spec_iff_natCast_eq_zero (R : CommRingCat.{u}) :
    SchemeCharP (Spec R) p ↔ (p : R) = 0 := by
  rw [iff_natCast_eq_zero]
  exact ⟨fun h ↦ by simpa using congr((Scheme.ΓSpecIso R).hom $h),
    fun h ↦ by simpa using congr((Scheme.ΓSpecIso R).inv $h)⟩

/-- On the spectrum of a nontrivial ring, intrinsic characteristic agrees with ring
characteristic. -/
@[simp]
theorem spec_iff (R : CommRingCat.{u}) [Nontrivial R] :
    SchemeCharP (Spec R) p ↔ CharP R p := by
  rw [spec_iff_natCast_eq_zero, CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]

/-- For prime `p`, intrinsic characteristic is equivalent to the existence of a structure
map to the prime field. Such a map is unique, including on the empty scheme. -/
theorem iff_structureMap : SchemeCharP X p ↔
    Nonempty (X ⟶ Spec (CommRingCat.of (ULift.{u} (ZMod p)))) := by
  refine ⟨fun h ↦ ⟨X.toSpecZMod (h.natCast_eq_zero ⊤)⟩, fun ⟨f⟩ ↦ ?_⟩
  have h : SchemeCharP (Spec (CommRingCat.of (ULift.{u} (ZMod p)))) p :=
    (spec_iff _).mpr inferInstance
  exact h.of_hom f

end SchemeCharP

variable {X Y S : Scheme.{u}} {p q : ℕ}

/-- The empty scheme has every stalkwise characteristic, although its section rings have
ring characteristic one. -/
instance [IsEmpty X] : SchemeCharP X p := ⟨fun x ↦ isEmptyElim x⟩

/-- A nonempty scheme cannot have two different stalkwise characteristics. -/
theorem SchemeCharP.eq [Nonempty X] (hp : SchemeCharP X p) (hq : SchemeCharP X q) :
    p = q := by
  let x : X := Classical.arbitrary X
  exact CharP.eq (X.presheaf.stalk x) (hp.charP_stalk x) (hq.charP_stalk x)

/-- Open subschemes inherit the characteristic of the ambient scheme for every natural
characteristic. -/
instance (U : X.Opens) [SchemeCharP X p] : SchemeCharP U p :=
  ⟨fun x ↦ charP_of_injective_ringHom
    (f := (U.ι.stalkMap x).hom) (ConcreteCategory.bijective_of_isIso _).1 p⟩

variable [Fact p.Prime]

/-- The base change of a characteristic-`p` scheme has characteristic `p`, with no
condition on the morphism used to change base. -/
instance (f : X ⟶ S) (g : Y ⟶ S) [h : SchemeCharP X p] :
    SchemeCharP (Limits.pullback f g) p :=
  h.of_hom (Limits.pullback.fst f g)

/-- Products inherit characteristic from either factor, here the first one. -/
instance [h : SchemeCharP X p] : SchemeCharP (Limits.prod X Y) p :=
  h.of_hom Limits.prod.fst

end TauCeti.AlgebraicGeometry
