/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.Algebra.Homology.TotallyAcyclic.Ext
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.Algebra.CharP.Frobenius.Finite
import TauCeti.Algebra.CharP.Frobenius.Flat
import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Higher Ext of Frobenius root modules on a hypersurface

Let `A = S/(w)` for a non-zero-divisor `w` of an F-finite regular ring. The module
obtained by restricting scalars on `A` along any iterate of Frobenius is Gorenstein-projective.
In particular, for a hypersurface in a regular algebra of finite type over a perfect ring of
prime characteristic,
its positive Ext groups into the ring (or any projective module) vanish. This applies to
the singular hypersurface cut out by the product of the coordinates of affine space.

Over the ambient ring the resolution is the ordinary sequence for multiplication by `w`,
with scalars restricted along Frobenius. Kunz's theorem and F-finiteness make its two
ambient terms finite projective. Eisenbud's hypersurface construction then gives a
complete resolution over the quotient.

## References

* B. Zavyalov, *Mod-p Poincaré Duality in p-adic analytic geometry*, Theorem 4.3.2,
  Step 1 (the higher Ext groups of the normal-crossing hypersurface).
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to
  group representations*, Trans. Amer. Math. Soc. **260** (1980), §5.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {S : Type u} [CommRing S] {w : S} (p : ℕ)

local notation "A" => S ⧸ Ideal.span (singleton w : Set S)

/-- Restriction along iterated Frobenius on a hypersurface in an F-finite regular ring
gives a Gorenstein-projective module, including at singular points of the hypersurface. -/
theorem isGorensteinProjective_restrictScalars_iterateFrobenius_quotient
    [ExpChar S p] [IsRegularRing S] [ExpChar A p] (hw : w ∈ nonZeroDivisors S)
    (hfin : (frobenius S p).Finite) (m : ℕ) :
    IsGorensteinProjective A ((ModuleCat.restrictScalars (iterateFrobenius A p m)).obj
      (ModuleCat.of A A)) := by
  let F := ModuleCat.restrictScalars (iterateFrobenius S p m)
  let P := F.obj (ModuleCat.of S S)
  have hfinite : (iterateFrobenius S p m).Finite := by
    induction m with
    | zero => simpa using RingHom.Finite.id S
    | succ m ih => simpa [iterateFrobenius_add, iterateFrobenius_one] using ih.comp hfin
  have : Module.Finite S P := hfinite
  have : Module.Flat S P := flat_iterateFrobenius p (IsRegularRing.flat_frobenius p) m
  have := Module.finitePresentation_of_finite S P
  have : Module.Projective S P := Module.Flat.projective_of_finitePresentation
  -- In the restricted sequence the first arrow still multiplies by the original equation.
  let π := Ideal.Quotient.mk (Ideal.span {w})
  let M := (ModuleCat.restrictScalars (iterateFrobenius A p m)).obj (ModuleCat.of A A)
  let d : FGModuleCat.of S P ⟶ FGModuleCat.of S P :=
    FGModuleCat.ofHom (F.map (ModuleCat.ofHom (LinearMap.mulLeft S w))).hom
  let g : P ⟶ (ModuleCat.restrictScalars π).obj M := ModuleCat.ofHom
    (X := P) (Y := (ModuleCat.restrictScalars π).obj M)
    { toFun := fun x ↦ π x
      map_add' := map_add π
      map_smul' r x :=
        (map_mul π _ _).trans (congrArg (· * π x) (π.map_iterateFrobenius p r m)) }
  -- Restriction preserves the underlying functions of both arrows.
  exact MatrixFactorization.isGorensteinProjective_of_exact (f := d) (g := g) hw
    (isRegular_iff_mem_nonZeroDivisors.mpr hw).left
    (Ideal.exact_mulLeft_mkₐ_span_singleton (R := S) w)
    (Ideal.Quotient.mk_surjective (I := Ideal.span {w}))

/-- On a hypersurface in a regular finite-type algebra over a perfect ring of characteristic
`p`, all positive Ext groups from the Frobenius root module to a projective module vanish. -/
theorem subsingleton_ext_restrictScalars_iterateFrobenius_quotient
    (k : Type*) [CommRing k] [Fact p.Prime] [CharP k p] [PerfectRing k p]
    [Algebra k S] [Algebra.FiniteType k S] [IsRegularRing S] [CharP A p]
    (hw : w ∈ nonZeroDivisors S) (m : ℕ) (Q : ModuleCat.{u} A) [Module.Projective A Q]
    {i : ℕ} (hi : 0 < i) :
    Subsingleton (Abelian.Ext
      ((ModuleCat.restrictScalars (iterateFrobenius A p m)).obj (ModuleCat.of A A)) Q i) := by
  -- The maps k → S → A force the characteristic of S to equal their common characteristic.
  have : CharP S p := ringChar.of_eq <| Nat.dvd_antisymm
    (CharP.dvd_of_ringHom (algebraMap k S) p (ringChar S))
    (CharP.dvd_of_ringHom (Ideal.Quotient.mk (Ideal.span {w})) (ringChar S) p)
  have hf := powRingHom_finite (CharP.cast_eq_zero S p) (algebraMap k S)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  rw [powRingHom_eq_frobenius] at hf
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  exact subsingleton_of_forall_eq 0
    ((isGorensteinProjective_restrictScalars_iterateFrobenius_quotient p hw hf m).ext_eq_zero Q)

end TauCeti
