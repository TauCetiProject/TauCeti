/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.NumberField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic

/-!
# Isogenies on Shafarevich–Tate groups

Let `f : W₁ → W₂` be a morphism of elliptic curves over a field `K`, and fix a family of field
extensions `L i` of `K` with embeddings `τ i : Kˢ → (L i)ˢ`. Since the map induced by `f` on
`H¹(G_K, E(Kˢ))` commutes with restriction to every `L i`, it preserves the classes that are
locally trivial along the family, and so restricts to a homomorphism of Shafarevich–Tate groups

```text
f.shafarevichTateMap τ : Sha(W₁) → Sha(W₂).
```

These maps are additive in `f` and functorial. Composing with the dual isogeny `f̂` gives
multiplication by `deg f` in either order, so the kernel of `f.shafarevichTateMap τ` lies in the
`deg f`-torsion of `Sha(W₁)`. Hence, whenever the `deg f`-torsion of both groups is finite, one
group is finite exactly when the other is (`TauCeti.Isogeny.Hom.finite_shafarevichTateGroup_iff`).

Over a number field the `m`-torsion of `Sha(E/K)` is finite for every `m ≠ 0`
(`WeierstrassCurve.finite_torsionBy_sha`, from the finiteness of the `m`-Selmer group). This gives
the **isogeny invariance of the finiteness of `Sha(E/K)`**
(`TauCeti.Isogeny.Hom.finite_sha_iff`): for a nonzero morphism `W₁ → W₂` over `K`, `Sha(W₁/K)` is
finite if and only if `Sha(W₂/K)` is. Finiteness itself is conjectural; this is the form in which
it enters the isogeny invariance of the Birch–Swinnerton-Dyer quotient (Cassels).

## Main definitions

* `TauCeti.Isogeny.Hom.shafarevichTateMap`: the map `Sha(W₁) → Sha(W₂)` induced by a morphism.

## Main results

* `TauCeti.Isogeny.Hom.shafarevichTateMap_dual_shafarevichTateMap`,
  `TauCeti.Isogeny.Hom.shafarevichTateMap_shafarevichTateMap_dual`: composing with the dual is
  multiplication by the degree.
* `TauCeti.Isogeny.Hom.ker_shafarevichTateMap_le_torsionBy`: the kernel is killed by the degree.
* `TauCeti.Isogeny.Hom.finite_shafarevichTateGroup_iff`: finiteness transfers along a morphism
  when the degree-torsion of both Shafarevich–Tate groups is finite.
* `TauCeti.Isogeny.Hom.finite_sha_iff`: over a number field, `Sha(W₁/K)` is finite if and only if
  `Sha(W₂/K)` is, for any nonzero morphism `W₁ → W₂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve TauCeti.ContCohomology

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-! ### The map on Shafarevich–Tate groups -/

/-- A morphism over `K` sends locally trivial classes to locally trivial classes. -/
theorem pointH1Map_mem_shafarevichTateGroup (f : Hom W₁.toAffine W₂.toAffine)
    {c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff} (hc : c ∈ W₁.shafarevichTateGroup τ) :
    f.pointH1Map c ∈ W₂.shafarevichTateGroup τ := by
  rw [mem_shafarevichTateGroup_iff] at hc ⊢
  intro i
  rw [pointRes_pointH1Map, hc i]
  exact map_zero _

/-- **The map `Sha(W₁) → Sha(W₂)`** induced by a morphism `f : W₁ → W₂` over `K`: the restriction
of `f.pointH1Map` to the classes that are locally trivial along `τ`. -/
def shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine) :
    W₁.shafarevichTateGroup τ →+ W₂.shafarevichTateGroup τ :=
  (f.pointH1Map.comp (W₁.shafarevichTateGroup τ).subtype).codRestrict _
    fun c ↦ f.pointH1Map_mem_shafarevichTateGroup τ c.2

/-- The map on Shafarevich–Tate groups is the map on first cohomology. -/
@[simp]
theorem coe_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₁.shafarevichTateGroup τ) :
    (f.shafarevichTateMap τ c : H1 (AbsoluteGaloisGroup K) W₂.PointCoeff) = f.pointH1Map c :=
  (rfl)

/-- The identity morphism acts identically on the Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_id : (id W₁.toAffine).shafarevichTateMap τ = AddMonoidHom.id _ := by
  ext c
  simp

/-- Composition of morphisms induces composition on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).shafarevichTateMap τ = (g.shafarevichTateMap τ).comp (f.shafarevichTateMap τ) := by
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
  ext c
  simp

/-- The zero morphism induces zero on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_zero : (0 : Hom W₁.toAffine W₂.toAffine).shafarevichTateMap τ = 0 := by
  ext c
  simp

/-- Multiplication by `n` on the curve induces multiplication by `n` on the Shafarevich–Tate
group. -/
@[simp]
theorem shafarevichTateMap_natCast (n : ℕ) (c : W₁.shafarevichTateGroup τ) :
    (n : Hom W₁.toAffine W₁.toAffine).shafarevichTateMap τ c = n • c := by
  ext
  simp

/-! ### The dual isogeny -/

/-- **A morphism followed by its dual is multiplication by the degree** on the Shafarevich–Tate
group. -/
@[simp]
theorem shafarevichTateMap_dual_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₁.shafarevichTateGroup τ) :
    f.dual.shafarevichTateMap τ (f.shafarevichTateMap τ c) = f.degree • c := by
  rw [← AddMonoidHom.comp_apply, ← shafarevichTateMap_comp, dual_comp_self, ← one_def, nsmul_one,
    shafarevichTateMap_natCast]

/-- **The dual of a morphism followed by the morphism is multiplication by the degree** on the
Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_shafarevichTateMap_dual (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₂.shafarevichTateGroup τ) :
    f.shafarevichTateMap τ (f.dual.shafarevichTateMap τ c) = f.degree • c := by
  rw [← AddMonoidHom.comp_apply, ← shafarevichTateMap_comp, comp_dual_self, ← one_def, nsmul_one,
    shafarevichTateMap_natCast]

/-- **The kernel of the map on Shafarevich–Tate groups is killed by the degree.** -/
theorem ker_shafarevichTateMap_le_torsionBy (f : Hom W₁.toAffine W₂.toAffine) :
    (f.shafarevichTateMap τ).ker ≤ AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree :=
  fun c hc ↦ AddSubgroup.torsionBy.nsmul_iff.2 <| by
    rw [← shafarevichTateMap_dual_shafarevichTateMap, AddMonoidHom.mem_ker.1 hc, map_zero]

/-! ### Finiteness -/

/-- If the `deg f`-torsion of `Sha(W₁)` is finite, then `Sha(W₁)` is finite as soon as `Sha(W₂)`
is: the kernel of `f.shafarevichTateMap τ` lies in that torsion. -/
theorem finite_shafarevichTateGroup_of_finite (f : Hom W₁.toAffine W₂.toAffine)
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree)]
    [Finite (W₂.shafarevichTateGroup τ)] : Finite (W₁.shafarevichTateGroup τ) :=
  have : Finite (f.shafarevichTateMap τ).ker := Finite.of_injective _
    (AddSubgroup.inclusion_injective (f.ker_shafarevichTateMap_le_torsionBy τ))
  (f.shafarevichTateMap τ).finite_iff_finite_ker_range.2 ⟨inferInstance, inferInstance⟩

/-- **Isogeny invariance of the finiteness of Shafarevich–Tate groups**: if the `deg f`-torsion
of both `Sha(W₁)` and `Sha(W₂)` is finite, then `Sha(W₁)` is finite if and only if `Sha(W₂)` is.
The converse direction goes through the dual of `f`, which has the same degree. -/
theorem finite_shafarevichTateGroup_iff (f : Hom W₁.toAffine W₂.toAffine)
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree)]
    [Finite (AddSubgroup.torsionBy (W₂.shafarevichTateGroup τ) f.degree)] :
    Finite (W₁.shafarevichTateGroup τ) ↔ Finite (W₂.shafarevichTateGroup τ) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ f.finite_shafarevichTateGroup_of_finite τ⟩
  have : Finite (AddSubgroup.torsionBy (W₂.shafarevichTateGroup τ) f.dual.degree) := by
    rwa [degree_dual]
  exact f.dual.finite_shafarevichTateGroup_of_finite τ

/-! ### Number fields -/

section NumberField

variable {K : Type*} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogeny invariance of the finiteness of `Sha(E/K)`** over a number field `K`: for a nonzero
morphism `f : W₁ → W₂` over `K`, the Shafarevich–Tate group of `W₁` is finite if and only if that
of `W₂` is, local triviality being required at every finite and infinite place. -/
theorem finite_sha_iff (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite W₁.sha ↔ Finite W₂.sha := by
  let τ (v : GlobalNumberFields.Place K) :
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion := IsSepClosed.lift
  have : NeZero f.degree := ⟨(f.degree_eq_zero_iff).not.2 hf⟩
  have h₁ := W₁.finite_torsionBy_sha f.degree
  have h₂ := W₂.finite_torsionBy_sha f.degree
  rw [W₁.sha_eq_shafarevichTateGroup τ] at h₁ ⊢
  rw [W₂.sha_eq_shafarevichTateGroup τ] at h₂ ⊢
  exact f.finite_shafarevichTateGroup_iff τ

end NumberField

end TauCeti.Isogeny.Hom
