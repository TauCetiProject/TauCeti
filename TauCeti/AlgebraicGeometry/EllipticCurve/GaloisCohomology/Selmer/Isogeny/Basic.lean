/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic

/-!
# Isogenies on Shafarevich–Tate groups

A morphism over the ground field preserves the classes that are trivial over a fixed family
of local fields. The resulting map on Shafarevich–Tate groups is functorial. Composing with the
dual gives multiplication by the degree, so its kernel is contained in degree-torsion.

These statements hold for any family of field extensions; in particular one can take all
completions of a number field, including its archimedean completions.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve ContCohomology

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- Morphisms preserve everywhere locally trivial first cohomology classes. -/
theorem pointH1Map_mem_shafarevichTateGroup (f : Hom W₁.toAffine W₂.toAffine)
    {c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff} (hc : c ∈ W₁.shafarevichTateGroup τ) :
    f.pointH1Map c ∈ W₂.shafarevichTateGroup τ := by
  rw [mem_shafarevichTateGroup_iff] at hc ⊢
  intro i
  rw [pointRes_pointH1Map, hc i]
  exact _root_.map_zero _

/-- The map on Shafarevich–Tate groups induced by a morphism of elliptic curves. -/
def shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine) :
    W₁.shafarevichTateGroup τ →+ W₂.shafarevichTateGroup τ :=
  (f.pointH1Map.comp (W₁.shafarevichTateGroup τ).subtype).codRestrict _
    fun c ↦ f.pointH1Map_mem_shafarevichTateGroup τ c.2

/-- The map on locally trivial classes is the restriction of the first cohomology map. -/
@[simp]
theorem coe_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₁.shafarevichTateGroup τ) :
    (f.shafarevichTateMap τ c : H1 (AbsoluteGaloisGroup K) W₂.PointCoeff) = f.pointH1Map c :=
  (rfl)

/-- The identity morphism acts identically on the Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_id :
    (id W₁.toAffine).shafarevichTateMap τ = AddMonoidHom.id _ := by
  ext c
  simp

/-- Composition of morphisms induces composition on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).shafarevichTateMap τ =
      (g.shafarevichTateMap τ).comp (f.shafarevichTateMap τ) := by
  ext c
  simp

/-- Addition of morphisms adds their induced maps on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).shafarevichTateMap τ = f.shafarevichTateMap τ + g.shafarevichTateMap τ := by
  ext c
  simp

/-- Negating a morphism negates its induced map on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).shafarevichTateMap τ = -f.shafarevichTateMap τ := by
  ext c
  simp

/-- Subtraction of morphisms subtracts their induced maps on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).shafarevichTateMap τ = f.shafarevichTateMap τ - g.shafarevichTateMap τ := by
  rw [sub_eq_add_neg, shafarevichTateMap_add, shafarevichTateMap_neg]
  exact (_root_.sub_eq_add_neg (f.shafarevichTateMap τ) (g.shafarevichTateMap τ)).symm

/-- Multiplication by `n` induces multiplication by `n` on the Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_natCast (n : ℕ) (c : W₁.shafarevichTateGroup τ) :
    (n : Hom W₁.toAffine W₁.toAffine).shafarevichTateMap τ c = n • c := by
  apply Subtype.ext
  rw [coe_shafarevichTateMap, AddSubgroup.coe_nsmul, pointH1Map_natCast]

/-- The zero morphism induces zero on the Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_zero :
    (0 : Hom W₁.toAffine W₂.toAffine).shafarevichTateMap τ = 0 := by
  ext c
  simp

/-- A morphism followed by its dual multiplies Shafarevich–Tate classes by its degree. -/
@[simp]
theorem shafarevichTateMap_dual_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₁.shafarevichTateGroup τ) :
    f.dual.shafarevichTateMap τ (f.shafarevichTateMap τ c) = f.degree • c := by
  rw [← AddMonoidHom.comp_apply, ← shafarevichTateMap_comp, dual_comp_self,
    ← one_def, nsmul_one, shafarevichTateMap_natCast]

/-- A dual morphism followed by the original multiplies classes by the original degree. -/
@[simp]
theorem shafarevichTateMap_shafarevichTateMap_dual (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₂.shafarevichTateGroup τ) :
    f.shafarevichTateMap τ (f.dual.shafarevichTateMap τ c) = f.degree • c := by
  rw [← AddMonoidHom.comp_apply, ← shafarevichTateMap_comp, comp_dual_self,
    ← one_def, nsmul_one, shafarevichTateMap_natCast]

/-- The kernel of the induced map is contained in degree-torsion. -/
theorem ker_shafarevichTateMap_le_torsionBy (f : Hom W₁.toAffine W₂.toAffine) :
    (f.shafarevichTateMap τ).ker ≤ AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree := by
  intro c hc
  rw [AddSubgroup.torsionBy.nsmul_iff]
  rw [← shafarevichTateMap_dual_shafarevichTateMap τ f c, AddMonoidHom.mem_ker.mp hc, map_zero]

end TauCeti.Isogeny.Hom

end
