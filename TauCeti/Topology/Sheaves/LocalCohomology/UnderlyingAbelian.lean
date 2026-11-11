/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.Basic
public import TauCeti.Topology.Sheaves.LocalCohomology.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.UnderlyingAbelian
import Mathlib.Topology.Sheaves.Forget

/-!
# Support truncation for local cohomology with module coefficients

Let `F` be a sheaf of `R`-modules on a topological space `X` and `S` a closed subset. The
cohomology `H_Sⁿ(W, F)` with supports in `S`, computed with module coefficients, agrees with the
cohomology with supports of the underlying abelian sheaf of `F`, compatibly with restriction
(`CategoryTheory.Sheaf.supportedModuleHPresheafForgetIso`). This file transfers support
truncation, and the identification of `H_Sⁿ(W, F)` with the sections of `𝓗_Sⁿ(F)` below the first
nonvanishing local cohomology sheaf, from `TauCeti.Topology.Sheaves.LocalCohomology.Basic` along
this comparison, keeping the `R`-module structures.

If the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules vanishes, every class in `H_Sⁿ(W, F)`
vanishes locally, so the local cohomology sheaf of the underlying abelian sheaf vanishes too
(`CategoryTheory.Sheaf.isZero_supportedHSheaf_of_isZero_supportedModuleHSheaf`). Consequently:

* **support truncation**: if `𝓗_S^q(F) = 0` for all `q < n`, then `H_S^q(W, F) = 0` for all
  `q < n` and every open `W`
  (`CategoryTheory.Sheaf.subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf`);
* under the same hypothesis, the presheaf of `R`-modules `W ↦ H_Sⁿ(W, F)` is already a sheaf
  (`CategoryTheory.Sheaf.isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf`), so the
  sheafification map is an `R`-linear isomorphism `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)`
  (`CategoryTheory.Sheaf.supportedModuleHSectionsEquiv`), compatible with restriction
  (`CategoryTheory.Sheaf.supportedModuleHSectionsEquiv_supportedModuleHPresheaf_map`).

For a real-analytic manifold `M` in a complexification, where purity gives `𝓗_M^q(𝓞) = 0` for
`q < n` with `𝓞` the sheaf of holomorphic functions, a sheaf of complex vector spaces, these give
`H_M^q(W, 𝓞) = 0` for `q < n` and identify the complex vector space `H_Mⁿ(W, 𝓞)` with the sections
of `𝓗_Mⁿ(𝓞)` over `W`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (S : Closeds X)

noncomputable section

/-- If the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules vanishes, then every class in
`H_Sⁿ(W, F)` vanishes locally: each point `x ∈ W` has an open neighbourhood `V ≤ W` on which the
class restricts to zero. -/
theorem exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : IsZero (F.supportedModuleHSheaf S n)) {W : Opens X} (c : F.supportedModuleH S W n)
    {x : X} (hx : x ∈ W) : ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧
      (F.supportedModuleHPresheaf S n).map (homOfLE hVW).op c = 0 :=
  TopCat.Presheaf.exists_map_eq_zero_of_isZero_presheafToSheaf_obj h c hx

/-- If the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules vanishes, so does the local cohomology
sheaf `𝓗_Sⁿ` of the underlying abelian sheaf of `F`. -/
theorem isZero_supportedHSheaf_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : IsZero (F.supportedModuleHSheaf S n)) :
    IsZero (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedHSheaf
      S n) := by
  refine (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff _).2 fun x W c hx ↦ ?_
  -- `c` is the image of a module-valued class, which vanishes locally
  obtain ⟨c, rfl⟩ := (F.supportedModuleHAddEquiv S W n).surjective c
  obtain ⟨V, hVW, hxV, hV⟩ :=
    F.exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf S h c hx
  exact ⟨V, hVW, hxV,
    (F.supportedModuleHAddEquiv_supportedModuleHPresheaf_map S (homOfLE hVW).op c).symm.trans
      ((congrArg _ hV).trans (map_zero _))⟩

/-- **Support truncation** for sheaves of `R`-modules: if the local cohomology sheaves `𝓗_S^q(F)`
vanish for all `q < n`, then the `R`-modules `H_S^q(W, F)` vanish for all `q < n` and every
open `W`. -/
theorem subsingleton_supportedModuleH_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) {q : ℕ} (hq : q < n) (W : Opens X) :
    Subsingleton (F.supportedModuleH S W q) :=
  have := subsingleton_supportedH_of_isZero_supportedHSheaf _ S
    (fun q hq ↦ F.isZero_supportedHSheaf_of_isZero_supportedModuleHSheaf S (h q hq)) hq W
  (F.supportedModuleHAddEquiv S W q).injective.subsingleton

/-- If the local cohomology sheaves `𝓗_S^q(F)` of `R`-modules vanish for all `q < n`, then the
presheaf of `R`-modules `W ↦ H_Sⁿ(W, F)` is already a sheaf. -/
theorem isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) :
    (F.supportedModuleHPresheaf S n).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _).2 <|
    (Presheaf.isSheaf_of_iso_iff (F.supportedModuleHPresheafForgetIso S n)).2 <|
      isSheaf_supportedHPresheaf_of_isZero_supportedHSheaf _ S fun q hq ↦
        F.isZero_supportedHSheaf_of_isZero_supportedModuleHSheaf S (h q hq)

variable {n : ℕ}

/-- **Edge comparison** for sheaves of `R`-modules: if the local cohomology sheaves `𝓗_S^q(F)`
vanish for all `q < n`, the sheafification map is an `R`-linear isomorphism from `H_Sⁿ(W, F)` to
the sections of `𝓗_Sⁿ(F)` over `W`. -/
def supportedModuleHSectionsEquiv (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q))
    (W : Opens X) :
    F.supportedModuleH S W n ≃ₗ[R] (F.supportedModuleHSheaf S n).obj.obj (op W) :=
  have :=
    isIso_toSheafify _ (F.isSheaf_supportedModuleHPresheaf_of_isZero_supportedModuleHSheaf S h)
  (asIso ((toSheafify _ (F.supportedModuleHPresheaf S n)).app (op W))).toLinearEquiv

/-- The edge comparison `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)` is the sheafification map. -/
@[simp]
lemma supportedModuleHSectionsEquiv_apply
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) (W : Opens X)
    (x : F.supportedModuleH S W n) :
    F.supportedModuleHSectionsEquiv S h W x =
      (toSheafify _ (F.supportedModuleHPresheaf S n)).app (op W) x :=
  (rfl)

/-- The edge comparison `H_Sⁿ(W, F) ≃ₗ[R] 𝓗_Sⁿ(F)(W)` is compatible with restriction to a
smaller open `W' ≤ W`. -/
lemma supportedModuleHSectionsEquiv_supportedModuleHPresheaf_map
    (h : ∀ q < n, IsZero (F.supportedModuleHSheaf S q)) {W' W : Opens X} (hW : W' ≤ W)
    (x : F.supportedModuleH S W n) :
    F.supportedModuleHSectionsEquiv S h W'
        ((F.supportedModuleHPresheaf S n).map (homOfLE hW).op x) =
      (F.supportedModuleHSheaf S n).obj.map (homOfLE hW).op
        (F.supportedModuleHSectionsEquiv S h W x) :=
  congr($((toSheafify _ (F.supportedModuleHPresheaf S n)).naturality (homOfLE hW).op) x)

end

end CategoryTheory.Sheaf
