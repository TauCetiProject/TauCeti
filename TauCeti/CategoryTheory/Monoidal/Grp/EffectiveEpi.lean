/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp

/-!
# Homomorphisms of group objects through an effective epimorphism

Let `f : G ⟶ H` be a homomorphism of group objects in a cartesian monoidal category which is an
effective epimorphism, and let `e : G ⟶ K` be a homomorphism of group objects. Then `e` factors
through `f` exactly when `e` kills the kernel of `f`, that is, when `x ≫ e = 1` for every point
`x` of `G` with `x ≫ f = 1`. Two points of `G` identified by `f` then differ by a point of the
kernel, so `e` identifies them too, and `e` descends along `f` (`TauCeti.homDesc`). The descended
morphism is a homomorphism as soon as `f ⊗ f` is an epimorphism. The kernel is described through
its points, so no kernel object needs to exist. Compare
`CategoryTheory.Grp.isColimitCokernelCoforkOfTorsor`, which gives the same factorization for a
chosen kernel object whose kernel pair is a torsor square.

For a homomorphism `f : G ⟶ H` of commutative group objects with the same hypotheses on `f`, and an
integer `n` killing the kernel of `f`, this factors multiplication by `n` on `G` through `f`. The
result is the **factorization dual** `CommGrp.factorizationDual f n : H ⟶ G`, the unique morphism
with `f ≫ f̂ = n`, and it also satisfies `f̂ ≫ f = n`. For an isogeny `f` of elliptic curves of
constant degree `n`, the kernel of `f` is finite locally free of rank `n`, so Deligne's theorem
says that `n` kills it, and `f̂` is the morphism underlying the expected dual isogeny, obtained by
factoring `[n]` through the quotient by the kernel: the target of `f` already is that quotient.
This file does not show that `f̂` is an isogeny. Over
a base scheme `S`, the hypotheses on `f` hold when its underlying morphism of schemes is flat,
surjective and quasi-compact (`CategoryTheory.Over.effectiveEpi_of_effectiveEpi_left`, Mathlib's
`AlgebraicGeometry.Sites.Fpqc`, and `AlgebraicGeometry.epi_tensorHom`).

## Main definitions

* `TauCeti.homDesc`: the homomorphism `H ⟶ K` through which a homomorphism `e : G ⟶ K` killing
  the kernel of an effective epimorphism `f : G ⟶ H` factors.
* `CategoryTheory.CommGrp.factorizationDual`: the factorization of multiplication by `n` through
  a homomorphism of commutative group objects whose kernel is killed by `n`.

## Main results

* `TauCeti.exists_comp_eq_iff_comp_eq_one`: `e` factors through `f` if and only if it kills the
  kernel of `f`.
* `CategoryTheory.CommGrp.comp_factorizationDual` and
  `CategoryTheory.CommGrp.factorizationDual_comp`: `f ≫ f̂ = n` and `f̂ ≫ f = n`.
* `CategoryTheory.CommGrp.eq_factorizationDual`: uniqueness of the factorization dual.
* `CategoryTheory.CommGrp.factorizationDual_comp_factorizationDual`: the factorization dual
  reverses composition.
* `CategoryTheory.CommGrp.factorizationDual_intCast`: the factorization dual of multiplication by
  `m` is multiplication by `m`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.4–2.5 (isogenies and their
  duals).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G H K : C} [GrpObj G] [GrpObj H] [GrpObj K] (f : G ⟶ H) [IsMonHom f] (e : G ⟶ K) [IsMonHom e]

/-- A homomorphism `e` killing the kernel of `f` identifies the points of `G` that `f` identifies:
they differ by a point of the kernel. -/
theorem comp_eq_comp_of_comp_eq_comp (he : ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ≫ e = 1)
    {Z : C} {g₁ g₂ : Z ⟶ G} (h : g₁ ≫ f = g₂ ≫ f) : g₁ ≫ e = g₂ ≫ e := by
  have hk := he (g₁ * g₂⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel])
  rwa [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one] at hk

/-- If `n` kills the kernel of `f : G ⟶ H` and `m` kills the kernel of `f' : H ⟶ L`, then
`m * n` kills the kernel of `f ≫ f'`. -/
theorem zpow_mul_eq_one_of_comp_comp_eq_one {L : C} [GrpObj L] {f' : H ⟶ L} {m n : ℤ}
    (hn : ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ^ n = 1)
    (hm : ∀ ⦃Z : C⦄ (y : Z ⟶ H), y ≫ f' = 1 → y ^ m = 1) {Z : C} (x : Z ⟶ G)
    (hx : x ≫ f ≫ f' = 1) : x ^ (m * n) = 1 := by
  rw [zpow_mul]
  exact hn _ (by rw [GrpObj.zpow_comp, hm _ (by rwa [← Category.assoc] at hx)])

variable [EffectiveEpi f]

/-- **Descent of a homomorphism along an effective epimorphism.** If `f : G ⟶ H` is a homomorphism
of group objects and an effective epimorphism, a homomorphism `e : G ⟶ K` killing the kernel of
`f` factors through `f` (`comp_homDesc`), uniquely (`eq_homDesc`). The factorization is a
homomorphism when `f ⊗ f` is an epimorphism (`isMonHom_homDesc`). -/
noncomputable def homDesc (he : ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ≫ e = 1) : H ⟶ K :=
  EffectiveEpi.desc f e fun _ _ h ↦ comp_eq_comp_of_comp_eq_comp f e he h

variable {f e}

/-- The descended homomorphism `homDesc f e he` factors `e` through `f`. -/
@[reassoc (attr := simp)]
theorem comp_homDesc (he : ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ≫ e = 1) :
    f ≫ homDesc f e he = e :=
  EffectiveEpi.fac f e _

/-- **Uniqueness of the descended homomorphism.** Every factorization of `e` through `f` is
`homDesc f e he`. -/
theorem eq_homDesc (he : ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ≫ e = 1) {d : H ⟶ K}
    (hd : f ≫ d = e) : d = homDesc f e he :=
  EffectiveEpi.uniq f e _ d hd

/-- The descended morphism `homDesc f e he` is a homomorphism of group objects when `f ⊗ f` is an
epimorphism. -/
instance isMonHom_homDesc [Epi (f ⊗ₘ f)]
    (he : ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ≫ e = 1) : IsMonHom (homDesc f e he) where
  one_hom := by
    rw [← IsMonHom.one_hom f, Category.assoc, comp_homDesc, IsMonHom.one_hom]
  mul_hom := by
    rw [← cancel_epi (f ⊗ₘ f)]
    simp [← IsMonHom.mul_hom_assoc f, tensorHom_comp_tensorHom_assoc]

variable (f e) in
/-- **Factorization through an effective epimorphism.** A homomorphism `e : G ⟶ K` factors
through a homomorphism `f : G ⟶ H` which is an effective epimorphism exactly when `e` kills the
kernel of `f`. -/
theorem exists_comp_eq_iff_comp_eq_one :
    (∃ d : H ⟶ K, f ≫ d = e) ↔ ∀ ⦃Z : C⦄ (x : Z ⟶ G), x ≫ f = 1 → x ≫ e = 1 := by
  refine ⟨fun ⟨d, hd⟩ Z x hx ↦ ?_, fun he ↦ ⟨homDesc f e he, comp_homDesc he⟩⟩
  rw [← hd, reassoc_of% hx, ← MonObj.one_comp (X := Z) f, Category.assoc, hd, MonObj.one_comp]

end TauCeti

namespace CategoryTheory.CommGrp

open TauCeti

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G H K : CommGrp C}

variable (f : G ⟶ H) [EffectiveEpi f.hom.hom.hom] [Epi (f.hom.hom.hom ⊗ₘ f.hom.hom.hom)]
  (n : ℤ)

/-- **The factorization dual.** Let `f : G ⟶ H` be a homomorphism of commutative group objects
which is an effective epimorphism, with `f ⊗ f` an epimorphism, and let `n` be an integer killing
the kernel of `f`. Then multiplication by `n` on `G` factors uniquely through `f`
(`comp_factorizationDual`, `eq_factorizationDual`), as a homomorphism `f̂ : H ⟶ G`, and
`f̂ ≫ f` is multiplication by `n` on `H` (`factorizationDual_comp`). For an isogeny of degree `n`
this is the morphism underlying the expected dual isogeny. -/
noncomputable def factorizationDual
    (hn : ∀ ⦃Z : C⦄ (x : Z ⟶ G.X), x ≫ f.hom.hom.hom = 1 → x ^ n = 1) : H ⟶ G :=
  homMk (homDesc f.hom.hom.hom (n : End G).hom.hom.hom fun _ x hx ↦ by
    rw [intCast_hom_hom_hom, GrpObj.comp_zpow, Category.comp_id]
    exact hn x hx)

variable {f n}

/-- If `f ⊗ f` and `f' ⊗ f'` are epimorphisms, so is `(f ≫ f') ⊗ (f ≫ f')`. -/
instance epi_tensorHom_comp_hom_hom_hom {f' : H ⟶ K}
    [Epi (f'.hom.hom.hom ⊗ₘ f'.hom.hom.hom)] :
    Epi ((f ≫ f').hom.hom.hom ⊗ₘ (f ≫ f').hom.hom.hom) := by
  simp only [comp_hom, Grp.comp', Mon.comp_hom', ← tensorHom_comp_tensorHom]
  infer_instance

/-- **The factorization dual factors multiplication by `n` through `f`:** `f ≫ f̂ = n`. -/
@[reassoc (attr := simp)]
theorem comp_factorizationDual
    (hn : ∀ ⦃Z : C⦄ (x : Z ⟶ G.X), x ≫ f.hom.hom.hom = 1 → x ^ n = 1) :
    f ≫ factorizationDual f n hn = (n : End G) :=
  hom_ext _ _ <| by simp [factorizationDual]

/-- **Uniqueness of the factorization dual.** A morphism `g : H ⟶ G` with `f ≫ g = n` is the
factorization dual. -/
theorem eq_factorizationDual
    (hn : ∀ ⦃Z : C⦄ (x : Z ⟶ G.X), x ≫ f.hom.hom.hom = 1 → x ^ n = 1) {g : H ⟶ G}
    (hg : f ≫ g = (n : End G)) : g = factorizationDual f n hn :=
  hom_ext _ _ <| by
    rw [factorizationDual, homMk_hom_hom_hom]
    exact eq_homDesc _ <| by simpa only [comp_hom, Grp.comp', Mon.comp_hom'] using
      congr($(hg).hom.hom.hom)

/-- **The factorization dual followed by `f` is multiplication by `n`:** `f̂ ≫ f = n`. -/
@[reassoc (attr := simp)]
theorem factorizationDual_comp
    (hn : ∀ ⦃Z : C⦄ (x : Z ⟶ G.X), x ≫ f.hom.hom.hom = 1 → x ^ n = 1) :
    factorizationDual f n hn ≫ f = (n : End H) := by
  have : Epi f := (CommGrp.forget C).epi_of_epi_map (inferInstanceAs (Epi f.hom.hom.hom))
  rw [← cancel_epi f, comp_factorizationDual_assoc]
  ext : 3
  simp [GrpObj.zpow_comp, GrpObj.comp_zpow]

variable (f n) in
/-- Multiplication by `n` factors through `f` exactly when `n` kills the kernel of `f`. -/
theorem exists_comp_eq_intCast_iff :
    (∃ g : H ⟶ G, f ≫ g = (n : End G)) ↔
      ∀ ⦃Z : C⦄ (x : Z ⟶ G.X), x ≫ f.hom.hom.hom = 1 → x ^ n = 1 := by
  refine ⟨fun ⟨g, hg⟩ Z x hx ↦ ?_, fun hn ↦ ⟨factorizationDual f n hn, comp_factorizationDual hn⟩⟩
  have := (exists_comp_eq_iff_comp_eq_one f.hom.hom.hom (n : End G).hom.hom.hom).1
    ⟨g.hom.hom.hom, by simpa only [comp_hom, Grp.comp', Mon.comp_hom'] using
      congr($(hg).hom.hom.hom)⟩ x hx
  rwa [intCast_hom_hom_hom, GrpObj.comp_zpow, Category.comp_id] at this

/-- **The factorization dual reverses composition.** If `n` kills the kernel of `f : G ⟶ H` and
`m` kills the kernel of `f' : H ⟶ K`, then `m * n` kills the kernel of `f ≫ f'`, and the
factorization dual of `f ≫ f'` is `f̂' ≫ f̂`. -/
@[simp]
theorem factorizationDual_comp_factorizationDual {f' : H ⟶ K} {m : ℤ}
    [EffectiveEpi f'.hom.hom.hom] [Epi (f'.hom.hom.hom ⊗ₘ f'.hom.hom.hom)]
    [EffectiveEpi (f ≫ f').hom.hom.hom]
    (hn : ∀ ⦃Z : C⦄ (x : Z ⟶ G.X), x ≫ f.hom.hom.hom = 1 → x ^ n = 1)
    (hm : ∀ ⦃Z : C⦄ (x : Z ⟶ H.X), x ≫ f'.hom.hom.hom = 1 → x ^ m = 1) :
    factorizationDual f' m hm ≫ factorizationDual f n hn =
      factorizationDual (f ≫ f') (m * n) (fun _ x hx ↦
        zpow_mul_eq_one_of_comp_comp_eq_one _ hn hm x (by simpa using hx)) := by
  refine eq_factorizationDual _ ?_
  have hc : (m : End G) ≫ f = f ≫ (m : End H) := by
    ext : 3
    simp [GrpObj.zpow_comp, GrpObj.comp_zpow]
  rw [Category.assoc, comp_factorizationDual_assoc, ← reassoc_of% hc, comp_factorizationDual,
    ← End.mul_def, ← Int.cast_mul, mul_comm]

variable (G) in
/-- **The factorization dual of multiplication by `m` relative to `m * k` is multiplication by
`k`.** Here `m * k` kills the kernel of multiplication by `m`. Taking `k = m` shows that the dual
of `[m]` relative to `m * m` is `[m]`. -/
@[simp]
theorem factorizationDual_intCast (m k : ℤ) [EffectiveEpi (m : End G).hom.hom.hom]
    [Epi ((m : End G).hom.hom.hom ⊗ₘ (m : End G).hom.hom.hom)] :
    factorizationDual (m : End G) (m * k) (fun _ x hx ↦ by
      rw [intCast_hom_hom_hom, GrpObj.comp_zpow, Category.comp_id] at hx
      rw [zpow_mul, hx, one_zpow]) = (k : End G) :=
  (eq_factorizationDual _ ((End.mul_def _ _).symm.trans <| by rw [← Int.cast_mul, mul_comm])).symm

end CategoryTheory.CommGrp
